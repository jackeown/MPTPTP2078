%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fcnry6ZNOP

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:04 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 485 expanded)
%              Number of leaves         :   39 ( 159 expanded)
%              Depth                    :   20
%              Number of atoms          : 1169 (9607 expanded)
%              Number of equality atoms :   32 ( 121 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
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
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('18',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_partfun1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('23',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_relat_1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != X21 )
      | ( v2_funct_2 @ X22 @ X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('42',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
      | ( v2_funct_2 @ X22 @ ( k2_relat_1 @ X22 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
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
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X5: $i] :
      ( ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('72',plain,(
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

thf('73',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36 ) )
      | ( v2_funct_1 @ X40 )
      | ( X38 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X37 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('79',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','57'])).

thf('85',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['83','84'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['70','85','86'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['67','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['58','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fcnry6ZNOP
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:38:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.53/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.73  % Solved by: fo/fo7.sh
% 0.53/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.73  % done 352 iterations in 0.276s
% 0.53/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.73  % SZS output start Refutation
% 0.53/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.73  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.53/0.73  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.53/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.53/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.53/0.73  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.53/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.53/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.53/0.73  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.53/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.53/0.73  thf(t29_funct_2, conjecture,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73       ( ![D:$i]:
% 0.53/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.73           ( ( r2_relset_1 @
% 0.53/0.73               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.53/0.73               ( k6_partfun1 @ A ) ) =>
% 0.53/0.73             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.73        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.73            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73          ( ![D:$i]:
% 0.53/0.73            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.73                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.73              ( ( r2_relset_1 @
% 0.53/0.73                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.53/0.73                  ( k6_partfun1 @ A ) ) =>
% 0.53/0.73                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.53/0.73    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.53/0.73  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.73      inference('split', [status(esa)], ['0'])).
% 0.53/0.73  thf('2', plain,
% 0.53/0.73      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.73        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.73        (k6_partfun1 @ sk_A))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(redefinition_k6_partfun1, axiom,
% 0.53/0.73    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.53/0.73  thf('3', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.73  thf('4', plain,
% 0.53/0.73      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.73        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.73        (k6_relat_1 @ sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.53/0.73  thf('5', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('6', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(dt_k1_partfun1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.73     ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.73         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.73         ( v1_funct_1 @ F ) & 
% 0.53/0.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.53/0.73       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.53/0.73         ( m1_subset_1 @
% 0.53/0.73           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.53/0.73           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.53/0.73  thf('7', plain,
% 0.53/0.73      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.53/0.73          | ~ (v1_funct_1 @ X23)
% 0.53/0.73          | ~ (v1_funct_1 @ X26)
% 0.53/0.73          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.53/0.73          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 0.53/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 0.53/0.73      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.53/0.73  thf('8', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.53/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.53/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.53/0.73          | ~ (v1_funct_1 @ X1)
% 0.53/0.73          | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.53/0.73  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('10', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.53/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.53/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.53/0.73          | ~ (v1_funct_1 @ X1))),
% 0.53/0.73      inference('demod', [status(thm)], ['8', '9'])).
% 0.53/0.73  thf('11', plain,
% 0.53/0.73      ((~ (v1_funct_1 @ sk_D)
% 0.53/0.73        | (m1_subset_1 @ 
% 0.53/0.73           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['5', '10'])).
% 0.53/0.73  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('13', plain,
% 0.53/0.73      ((m1_subset_1 @ 
% 0.53/0.73        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.53/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.53/0.73  thf(redefinition_r2_relset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.73     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.53/0.73  thf('14', plain,
% 0.53/0.73      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.53/0.73          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.53/0.73          | ((X17) = (X20))
% 0.53/0.73          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.53/0.73  thf('15', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.73             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.53/0.73          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.53/0.73  thf('16', plain,
% 0.53/0.73      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.53/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.53/0.73        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.73            = (k6_relat_1 @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['4', '15'])).
% 0.53/0.73  thf(dt_k6_partfun1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( m1_subset_1 @
% 0.53/0.73         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.53/0.73       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.53/0.73  thf('17', plain,
% 0.53/0.73      (![X30 : $i]:
% 0.53/0.73         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 0.53/0.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.53/0.73      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.53/0.73  thf('18', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.73  thf('19', plain,
% 0.53/0.73      (![X30 : $i]:
% 0.53/0.73         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 0.53/0.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.53/0.73      inference('demod', [status(thm)], ['17', '18'])).
% 0.53/0.73  thf('20', plain,
% 0.53/0.73      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.73         = (k6_relat_1 @ sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['16', '19'])).
% 0.53/0.73  thf('21', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t24_funct_2, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73       ( ![D:$i]:
% 0.53/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.73           ( ( r2_relset_1 @
% 0.53/0.73               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.53/0.73               ( k6_partfun1 @ B ) ) =>
% 0.53/0.73             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.53/0.73  thf('22', plain,
% 0.53/0.73      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X32)
% 0.53/0.73          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.53/0.73          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.53/0.73          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 0.53/0.73               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 0.53/0.73               (k6_partfun1 @ X33))
% 0.53/0.73          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 0.53/0.73          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.53/0.73          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.53/0.73          | ~ (v1_funct_1 @ X35))),
% 0.53/0.73      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.53/0.73  thf('23', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.73  thf('24', plain,
% 0.53/0.73      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X32)
% 0.53/0.73          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.53/0.73          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.53/0.73          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 0.53/0.73               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 0.53/0.73               (k6_relat_1 @ X33))
% 0.53/0.73          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 0.53/0.73          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.53/0.73          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.53/0.73          | ~ (v1_funct_1 @ X35))),
% 0.53/0.73      inference('demod', [status(thm)], ['22', '23'])).
% 0.53/0.73  thf('25', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X0)
% 0.53/0.73          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.73          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.53/0.73          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.73               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.53/0.73               (k6_relat_1 @ sk_A))
% 0.53/0.73          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.53/0.73          | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['21', '24'])).
% 0.53/0.73  thf('26', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('28', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X0)
% 0.53/0.73          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.73          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.53/0.73          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.73               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.53/0.73               (k6_relat_1 @ sk_A)))),
% 0.53/0.73      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.53/0.73  thf('29', plain,
% 0.53/0.73      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.53/0.73           (k6_relat_1 @ sk_A))
% 0.53/0.73        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.53/0.73        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.73        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.53/0.73        | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['20', '28'])).
% 0.53/0.73  thf('30', plain,
% 0.53/0.73      (![X30 : $i]:
% 0.53/0.73         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 0.53/0.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.53/0.73      inference('demod', [status(thm)], ['17', '18'])).
% 0.53/0.73  thf('31', plain,
% 0.53/0.73      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.53/0.73          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.53/0.73          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 0.53/0.73          | ((X17) != (X20)))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.53/0.73  thf('32', plain,
% 0.53/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.73         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.53/0.73          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.53/0.73      inference('simplify', [status(thm)], ['31'])).
% 0.53/0.73  thf('33', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['30', '32'])).
% 0.53/0.73  thf('34', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.53/0.73  thf('35', plain,
% 0.53/0.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.73         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.53/0.73          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.53/0.73  thf('36', plain,
% 0.53/0.73      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.73  thf('37', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('40', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['29', '33', '36', '37', '38', '39'])).
% 0.53/0.73  thf(d3_funct_2, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.53/0.73       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.53/0.73  thf('41', plain,
% 0.53/0.73      (![X21 : $i, X22 : $i]:
% 0.53/0.73         (((k2_relat_1 @ X22) != (X21))
% 0.53/0.73          | (v2_funct_2 @ X22 @ X21)
% 0.53/0.73          | ~ (v5_relat_1 @ X22 @ X21)
% 0.53/0.73          | ~ (v1_relat_1 @ X22))),
% 0.53/0.73      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.53/0.73  thf('42', plain,
% 0.53/0.73      (![X22 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X22)
% 0.53/0.73          | ~ (v5_relat_1 @ X22 @ (k2_relat_1 @ X22))
% 0.53/0.73          | (v2_funct_2 @ X22 @ (k2_relat_1 @ X22)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['41'])).
% 0.53/0.73  thf('43', plain,
% 0.53/0.73      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.53/0.73        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.53/0.73        | ~ (v1_relat_1 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['40', '42'])).
% 0.53/0.73  thf('44', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(cc2_relset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.53/0.73  thf('45', plain,
% 0.53/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.53/0.73         ((v5_relat_1 @ X8 @ X10)
% 0.53/0.73          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.53/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.53/0.73  thf('46', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.53/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.53/0.73  thf('47', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['29', '33', '36', '37', '38', '39'])).
% 0.53/0.73  thf('48', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(cc2_relat_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ A ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.53/0.73  thf('49', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.53/0.73          | (v1_relat_1 @ X0)
% 0.53/0.73          | ~ (v1_relat_1 @ X1))),
% 0.53/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.73  thf('50', plain,
% 0.53/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['48', '49'])).
% 0.53/0.73  thf(fc6_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.53/0.73  thf('51', plain,
% 0.53/0.73      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.73  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.73      inference('demod', [status(thm)], ['50', '51'])).
% 0.53/0.73  thf('53', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.53/0.73      inference('demod', [status(thm)], ['43', '46', '47', '52'])).
% 0.53/0.73  thf('54', plain,
% 0.53/0.73      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.53/0.73      inference('split', [status(esa)], ['0'])).
% 0.53/0.73  thf('55', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.73      inference('sup-', [status(thm)], ['53', '54'])).
% 0.53/0.73  thf('56', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.73      inference('split', [status(esa)], ['0'])).
% 0.53/0.73  thf('57', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.53/0.73      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.53/0.73  thf('58', plain, (~ (v2_funct_1 @ sk_C)),
% 0.53/0.73      inference('simpl_trail', [status(thm)], ['1', '57'])).
% 0.53/0.73  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(cc2_funct_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.53/0.73       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.53/0.73  thf('60', plain,
% 0.53/0.73      (![X5 : $i]:
% 0.53/0.73         ((v2_funct_1 @ X5)
% 0.53/0.73          | ~ (v1_funct_1 @ X5)
% 0.53/0.73          | ~ (v1_relat_1 @ X5)
% 0.53/0.73          | ~ (v1_xboole_0 @ X5))),
% 0.53/0.73      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.53/0.73  thf('61', plain,
% 0.53/0.73      ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C) | (v2_funct_1 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['59', '60'])).
% 0.53/0.73  thf('62', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('63', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.53/0.73          | (v1_relat_1 @ X0)
% 0.53/0.73          | ~ (v1_relat_1 @ X1))),
% 0.53/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.73  thf('64', plain,
% 0.53/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.73  thf('65', plain,
% 0.53/0.73      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.73  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['64', '65'])).
% 0.53/0.73  thf('67', plain, ((~ (v1_xboole_0 @ sk_C) | (v2_funct_1 @ sk_C))),
% 0.53/0.73      inference('demod', [status(thm)], ['61', '66'])).
% 0.53/0.73  thf('68', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(cc3_relset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( v1_xboole_0 @ A ) =>
% 0.53/0.73       ( ![C:$i]:
% 0.53/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.73           ( v1_xboole_0 @ C ) ) ) ))).
% 0.53/0.73  thf('69', plain,
% 0.53/0.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.73         (~ (v1_xboole_0 @ X11)
% 0.53/0.73          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X13)))
% 0.53/0.73          | (v1_xboole_0 @ X12))),
% 0.53/0.73      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.53/0.73  thf('70', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 0.53/0.73      inference('sup-', [status(thm)], ['68', '69'])).
% 0.53/0.73  thf('71', plain,
% 0.53/0.73      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.73         = (k6_relat_1 @ sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['16', '19'])).
% 0.53/0.73  thf('72', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t26_funct_2, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73       ( ![E:$i]:
% 0.53/0.73         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.53/0.73             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.53/0.73           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.53/0.73             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.53/0.73               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.53/0.73  thf('73', plain,
% 0.53/0.73      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X36)
% 0.53/0.73          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.53/0.73          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.53/0.73          | ~ (v2_funct_1 @ (k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36))
% 0.53/0.73          | (v2_funct_1 @ X40)
% 0.53/0.73          | ((X38) = (k1_xboole_0))
% 0.53/0.73          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.53/0.73          | ~ (v1_funct_2 @ X40 @ X39 @ X37)
% 0.53/0.73          | ~ (v1_funct_1 @ X40))),
% 0.53/0.73      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.53/0.73  thf('74', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X0)
% 0.53/0.73          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.53/0.73          | ((sk_A) = (k1_xboole_0))
% 0.53/0.73          | (v2_funct_1 @ X0)
% 0.53/0.73          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.53/0.73          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.53/0.73          | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['72', '73'])).
% 0.53/0.73  thf('75', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('77', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X0)
% 0.53/0.73          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.53/0.73          | ((sk_A) = (k1_xboole_0))
% 0.53/0.73          | (v2_funct_1 @ X0)
% 0.53/0.73          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.53/0.73      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.53/0.73  thf('78', plain,
% 0.53/0.73      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.53/0.73        | (v2_funct_1 @ sk_C)
% 0.53/0.73        | ((sk_A) = (k1_xboole_0))
% 0.53/0.73        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.53/0.73        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.53/0.73        | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['71', '77'])).
% 0.53/0.73  thf(fc4_funct_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.53/0.73       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.53/0.73  thf('79', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.53/0.73  thf('80', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('81', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('83', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.53/0.73  thf('84', plain, (~ (v2_funct_1 @ sk_C)),
% 0.53/0.73      inference('simpl_trail', [status(thm)], ['1', '57'])).
% 0.53/0.73  thf('85', plain, (((sk_A) = (k1_xboole_0))),
% 0.53/0.73      inference('clc', [status(thm)], ['83', '84'])).
% 0.53/0.73  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.53/0.73  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.73  thf('87', plain, ((v1_xboole_0 @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['70', '85', '86'])).
% 0.53/0.73  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.53/0.73      inference('demod', [status(thm)], ['67', '87'])).
% 0.53/0.73  thf('89', plain, ($false), inference('demod', [status(thm)], ['58', '88'])).
% 0.53/0.73  
% 0.53/0.73  % SZS output end Refutation
% 0.53/0.73  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
