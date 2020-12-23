%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JTRL9ZWjyP

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:55 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  275 (1264 expanded)
%              Number of leaves         :   43 ( 412 expanded)
%              Depth                    :   44
%              Number of atoms          : 2194 (23975 expanded)
%              Number of equality atoms :  129 (1676 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X37 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
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
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('28',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('32',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('34',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('36',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('43',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['51','54','55','56'])).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['35','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('83',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('84',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('90',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['81','82','85','86','87','88','89'])).

thf('91',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('95',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['93','94','95','96','97','98'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('100',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('101',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('102',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('103',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('104',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('105',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['99','108'])).

thf('110',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['31','109'])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('112',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('113',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('114',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('115',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('116',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('117',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('118',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_partfun1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','121','122','123','124'])).

thf('126',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('127',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('129',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('131',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['129','132'])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','133'])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('136',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['134','135','136','137','138','139'])).

thf('141',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['29','140'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['141','142','143','144','145','146'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('148',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['25','155'])).

thf('157',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('158',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('159',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('164',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['161','164'])).

thf('166',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['162','163'])).

thf('169',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['162','163'])).

thf('171',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','169','170'])).

thf('172',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('173',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('174',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('175',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('177',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('179',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70','71'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('181',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['177','185','186','187','188'])).

thf('190',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['172','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('192',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['167','168'])).

thf('195',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('196',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_partfun1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('197',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('199',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('203',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['204','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['194','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['162','163'])).

thf('211',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['162','163'])).

thf('212',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('214',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf('216',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('217',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('219',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('221',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('223',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf('225',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('226',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['214','215','216','223','224','225'])).

thf('227',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['193','226'])).

thf('228',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference('sup+',[status(thm)],['171','227'])).

thf('229',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['228','229'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JTRL9ZWjyP
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:46:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.20/1.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.45  % Solved by: fo/fo7.sh
% 1.20/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.45  % done 1527 iterations in 0.990s
% 1.20/1.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.45  % SZS output start Refutation
% 1.20/1.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.20/1.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.45  thf(sk_C_type, type, sk_C: $i).
% 1.20/1.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.20/1.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.20/1.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.20/1.45  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.20/1.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.20/1.45  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.20/1.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.20/1.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.20/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.20/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.45  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.20/1.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.20/1.45  thf(sk_D_type, type, sk_D: $i).
% 1.20/1.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.20/1.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.20/1.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.20/1.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.45  thf(t36_funct_2, conjecture,
% 1.20/1.45    (![A:$i,B:$i,C:$i]:
% 1.20/1.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.45       ( ![D:$i]:
% 1.20/1.45         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.45             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.45           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.20/1.45               ( r2_relset_1 @
% 1.20/1.45                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.20/1.45                 ( k6_partfun1 @ A ) ) & 
% 1.20/1.45               ( v2_funct_1 @ C ) ) =>
% 1.20/1.45             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.20/1.45               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.20/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.45    (~( ![A:$i,B:$i,C:$i]:
% 1.20/1.45        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.45            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.45          ( ![D:$i]:
% 1.20/1.45            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.45                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.45              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.20/1.45                  ( r2_relset_1 @
% 1.20/1.45                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.20/1.45                    ( k6_partfun1 @ A ) ) & 
% 1.20/1.45                  ( v2_funct_1 @ C ) ) =>
% 1.20/1.45                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.20/1.45                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.20/1.45    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.20/1.45  thf('0', plain,
% 1.20/1.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('1', plain,
% 1.20/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf(redefinition_k1_partfun1, axiom,
% 1.20/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.20/1.45     ( ( ( v1_funct_1 @ E ) & 
% 1.20/1.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.45         ( v1_funct_1 @ F ) & 
% 1.20/1.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.20/1.45       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.20/1.45  thf('2', plain,
% 1.20/1.45      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.20/1.45         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.20/1.45          | ~ (v1_funct_1 @ X38)
% 1.20/1.45          | ~ (v1_funct_1 @ X41)
% 1.20/1.45          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.20/1.45          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 1.20/1.45              = (k5_relat_1 @ X38 @ X41)))),
% 1.20/1.45      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.20/1.45  thf('3', plain,
% 1.20/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.45         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.20/1.45            = (k5_relat_1 @ sk_C @ X0))
% 1.20/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.20/1.45          | ~ (v1_funct_1 @ X0)
% 1.20/1.45          | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.45      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.45  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('5', plain,
% 1.20/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.45         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.20/1.45            = (k5_relat_1 @ sk_C @ X0))
% 1.20/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.20/1.45          | ~ (v1_funct_1 @ X0))),
% 1.20/1.45      inference('demod', [status(thm)], ['3', '4'])).
% 1.20/1.45  thf('6', plain,
% 1.20/1.45      ((~ (v1_funct_1 @ sk_D)
% 1.20/1.45        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.45            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.20/1.45      inference('sup-', [status(thm)], ['0', '5'])).
% 1.20/1.45  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('8', plain,
% 1.20/1.45      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.45        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.45        (k6_partfun1 @ sk_A))),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('9', plain,
% 1.20/1.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('10', plain,
% 1.20/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf(dt_k1_partfun1, axiom,
% 1.20/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.20/1.45     ( ( ( v1_funct_1 @ E ) & 
% 1.20/1.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.45         ( v1_funct_1 @ F ) & 
% 1.20/1.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.20/1.45       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.20/1.45         ( m1_subset_1 @
% 1.20/1.45           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.20/1.45           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.20/1.45  thf('11', plain,
% 1.20/1.45      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.20/1.45         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.20/1.45          | ~ (v1_funct_1 @ X32)
% 1.20/1.45          | ~ (v1_funct_1 @ X35)
% 1.20/1.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.20/1.45          | (m1_subset_1 @ (k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35) @ 
% 1.20/1.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X37))))),
% 1.20/1.45      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.20/1.45  thf('12', plain,
% 1.20/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.45         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.20/1.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.20/1.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.20/1.45          | ~ (v1_funct_1 @ X1)
% 1.20/1.45          | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.45      inference('sup-', [status(thm)], ['10', '11'])).
% 1.20/1.45  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('14', plain,
% 1.20/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.45         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.20/1.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.20/1.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.20/1.45          | ~ (v1_funct_1 @ X1))),
% 1.20/1.45      inference('demod', [status(thm)], ['12', '13'])).
% 1.20/1.45  thf('15', plain,
% 1.20/1.45      ((~ (v1_funct_1 @ sk_D)
% 1.20/1.45        | (m1_subset_1 @ 
% 1.20/1.45           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.20/1.45      inference('sup-', [status(thm)], ['9', '14'])).
% 1.20/1.45  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('17', plain,
% 1.20/1.45      ((m1_subset_1 @ 
% 1.20/1.45        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.20/1.45      inference('demod', [status(thm)], ['15', '16'])).
% 1.20/1.45  thf(redefinition_r2_relset_1, axiom,
% 1.20/1.45    (![A:$i,B:$i,C:$i,D:$i]:
% 1.20/1.45     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.45       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.20/1.45  thf('18', plain,
% 1.20/1.45      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.20/1.45         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.20/1.45          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.20/1.45          | ((X27) = (X30))
% 1.20/1.45          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 1.20/1.45      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.20/1.45  thf('19', plain,
% 1.20/1.45      (![X0 : $i]:
% 1.20/1.45         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.45             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.20/1.45          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.20/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.20/1.45      inference('sup-', [status(thm)], ['17', '18'])).
% 1.20/1.45  thf('20', plain,
% 1.20/1.45      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.20/1.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.20/1.45        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.45            = (k6_partfun1 @ sk_A)))),
% 1.20/1.45      inference('sup-', [status(thm)], ['8', '19'])).
% 1.20/1.45  thf(t29_relset_1, axiom,
% 1.20/1.45    (![A:$i]:
% 1.20/1.45     ( m1_subset_1 @
% 1.20/1.45       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.20/1.45  thf('21', plain,
% 1.20/1.45      (![X31 : $i]:
% 1.20/1.45         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 1.20/1.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 1.20/1.45      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.20/1.45  thf(redefinition_k6_partfun1, axiom,
% 1.20/1.45    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.20/1.45  thf('22', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 1.20/1.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.45  thf('23', plain,
% 1.20/1.45      (![X31 : $i]:
% 1.20/1.45         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 1.20/1.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 1.20/1.45      inference('demod', [status(thm)], ['21', '22'])).
% 1.20/1.45  thf('24', plain,
% 1.20/1.45      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.45         = (k6_partfun1 @ sk_A))),
% 1.20/1.45      inference('demod', [status(thm)], ['20', '23'])).
% 1.20/1.45  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.45      inference('demod', [status(thm)], ['6', '7', '24'])).
% 1.20/1.45  thf(dt_k2_funct_1, axiom,
% 1.20/1.45    (![A:$i]:
% 1.20/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.45       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.20/1.45         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.20/1.45  thf('26', plain,
% 1.20/1.45      (![X15 : $i]:
% 1.20/1.45         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.20/1.45          | ~ (v1_funct_1 @ X15)
% 1.20/1.45          | ~ (v1_relat_1 @ X15))),
% 1.20/1.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.45  thf(t61_funct_1, axiom,
% 1.20/1.45    (![A:$i]:
% 1.20/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.45       ( ( v2_funct_1 @ A ) =>
% 1.20/1.45         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.20/1.45             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.20/1.45           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.20/1.45             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.20/1.45  thf('27', plain,
% 1.20/1.45      (![X17 : $i]:
% 1.20/1.45         (~ (v2_funct_1 @ X17)
% 1.20/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.20/1.45              = (k6_relat_1 @ (k2_relat_1 @ X17)))
% 1.20/1.45          | ~ (v1_funct_1 @ X17)
% 1.20/1.45          | ~ (v1_relat_1 @ X17))),
% 1.20/1.45      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.45  thf('28', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 1.20/1.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.45  thf('29', plain,
% 1.20/1.45      (![X17 : $i]:
% 1.20/1.45         (~ (v2_funct_1 @ X17)
% 1.20/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.20/1.45              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.20/1.45          | ~ (v1_funct_1 @ X17)
% 1.20/1.45          | ~ (v1_relat_1 @ X17))),
% 1.20/1.45      inference('demod', [status(thm)], ['27', '28'])).
% 1.20/1.45  thf('30', plain,
% 1.20/1.45      (![X17 : $i]:
% 1.20/1.45         (~ (v2_funct_1 @ X17)
% 1.20/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.20/1.45              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.20/1.45          | ~ (v1_funct_1 @ X17)
% 1.20/1.45          | ~ (v1_relat_1 @ X17))),
% 1.20/1.45      inference('demod', [status(thm)], ['27', '28'])).
% 1.20/1.45  thf('31', plain,
% 1.20/1.45      (![X17 : $i]:
% 1.20/1.45         (~ (v2_funct_1 @ X17)
% 1.20/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.20/1.45              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.20/1.45          | ~ (v1_funct_1 @ X17)
% 1.20/1.45          | ~ (v1_relat_1 @ X17))),
% 1.20/1.45      inference('demod', [status(thm)], ['27', '28'])).
% 1.20/1.45  thf('32', plain,
% 1.20/1.45      (![X17 : $i]:
% 1.20/1.45         (~ (v2_funct_1 @ X17)
% 1.20/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.20/1.45              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.20/1.45          | ~ (v1_funct_1 @ X17)
% 1.20/1.45          | ~ (v1_relat_1 @ X17))),
% 1.20/1.45      inference('demod', [status(thm)], ['27', '28'])).
% 1.20/1.45  thf('33', plain,
% 1.20/1.45      (![X17 : $i]:
% 1.20/1.45         (~ (v2_funct_1 @ X17)
% 1.20/1.45          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.20/1.45              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.20/1.45          | ~ (v1_funct_1 @ X17)
% 1.20/1.45          | ~ (v1_relat_1 @ X17))),
% 1.20/1.45      inference('demod', [status(thm)], ['27', '28'])).
% 1.20/1.45  thf('34', plain,
% 1.20/1.45      (![X15 : $i]:
% 1.20/1.45         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.20/1.45          | ~ (v1_funct_1 @ X15)
% 1.20/1.45          | ~ (v1_relat_1 @ X15))),
% 1.20/1.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.45  thf(t55_funct_1, axiom,
% 1.20/1.45    (![A:$i]:
% 1.20/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.45       ( ( v2_funct_1 @ A ) =>
% 1.20/1.45         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.20/1.45           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.20/1.45  thf('35', plain,
% 1.20/1.45      (![X16 : $i]:
% 1.20/1.45         (~ (v2_funct_1 @ X16)
% 1.20/1.45          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 1.20/1.45          | ~ (v1_funct_1 @ X16)
% 1.20/1.45          | ~ (v1_relat_1 @ X16))),
% 1.20/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.45  thf('36', plain,
% 1.20/1.45      (![X15 : $i]:
% 1.20/1.45         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.20/1.45          | ~ (v1_funct_1 @ X15)
% 1.20/1.45          | ~ (v1_relat_1 @ X15))),
% 1.20/1.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.45  thf('37', plain,
% 1.20/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf(redefinition_k2_relset_1, axiom,
% 1.20/1.45    (![A:$i,B:$i,C:$i]:
% 1.20/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.20/1.45  thf('38', plain,
% 1.20/1.45      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.20/1.45         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 1.20/1.45          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.20/1.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.20/1.45  thf('39', plain,
% 1.20/1.45      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.20/1.45      inference('sup-', [status(thm)], ['37', '38'])).
% 1.20/1.45  thf('40', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('41', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.45      inference('sup+', [status(thm)], ['39', '40'])).
% 1.20/1.45  thf('42', plain,
% 1.20/1.45      (![X15 : $i]:
% 1.20/1.45         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.20/1.45          | ~ (v1_funct_1 @ X15)
% 1.20/1.45          | ~ (v1_relat_1 @ X15))),
% 1.20/1.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.45  thf('43', plain,
% 1.20/1.45      (![X16 : $i]:
% 1.20/1.45         (~ (v2_funct_1 @ X16)
% 1.20/1.45          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 1.20/1.45          | ~ (v1_funct_1 @ X16)
% 1.20/1.45          | ~ (v1_relat_1 @ X16))),
% 1.20/1.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.45  thf(d10_xboole_0, axiom,
% 1.20/1.45    (![A:$i,B:$i]:
% 1.20/1.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.20/1.45  thf('44', plain,
% 1.20/1.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.20/1.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.45  thf('45', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.45      inference('simplify', [status(thm)], ['44'])).
% 1.20/1.45  thf(d18_relat_1, axiom,
% 1.20/1.45    (![A:$i,B:$i]:
% 1.20/1.45     ( ( v1_relat_1 @ B ) =>
% 1.20/1.45       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.20/1.45  thf('46', plain,
% 1.20/1.45      (![X3 : $i, X4 : $i]:
% 1.20/1.45         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.45          | (v4_relat_1 @ X3 @ X4)
% 1.20/1.45          | ~ (v1_relat_1 @ X3))),
% 1.20/1.45      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.45  thf('47', plain,
% 1.20/1.45      (![X0 : $i]:
% 1.20/1.45         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.20/1.45      inference('sup-', [status(thm)], ['45', '46'])).
% 1.20/1.45  thf('48', plain,
% 1.20/1.45      (![X0 : $i]:
% 1.20/1.45         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.20/1.45          | ~ (v1_relat_1 @ X0)
% 1.20/1.45          | ~ (v1_funct_1 @ X0)
% 1.20/1.45          | ~ (v2_funct_1 @ X0)
% 1.20/1.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.45      inference('sup+', [status(thm)], ['43', '47'])).
% 1.20/1.45  thf('49', plain,
% 1.20/1.45      (![X0 : $i]:
% 1.20/1.45         (~ (v1_relat_1 @ X0)
% 1.20/1.45          | ~ (v1_funct_1 @ X0)
% 1.20/1.45          | ~ (v2_funct_1 @ X0)
% 1.20/1.45          | ~ (v1_funct_1 @ X0)
% 1.20/1.45          | ~ (v1_relat_1 @ X0)
% 1.20/1.45          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.20/1.45      inference('sup-', [status(thm)], ['42', '48'])).
% 1.20/1.45  thf('50', plain,
% 1.20/1.45      (![X0 : $i]:
% 1.20/1.45         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.20/1.45          | ~ (v2_funct_1 @ X0)
% 1.20/1.45          | ~ (v1_funct_1 @ X0)
% 1.20/1.45          | ~ (v1_relat_1 @ X0))),
% 1.20/1.45      inference('simplify', [status(thm)], ['49'])).
% 1.20/1.45  thf('51', plain,
% 1.20/1.45      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.20/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.20/1.45      inference('sup+', [status(thm)], ['41', '50'])).
% 1.20/1.45  thf('52', plain,
% 1.20/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf(cc1_relset_1, axiom,
% 1.20/1.45    (![A:$i,B:$i,C:$i]:
% 1.20/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.45       ( v1_relat_1 @ C ) ))).
% 1.20/1.45  thf('53', plain,
% 1.20/1.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.20/1.45         ((v1_relat_1 @ X18)
% 1.20/1.45          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.20/1.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.20/1.45  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.45      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.45  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('57', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.20/1.45      inference('demod', [status(thm)], ['51', '54', '55', '56'])).
% 1.20/1.45  thf('58', plain,
% 1.20/1.45      (![X3 : $i, X4 : $i]:
% 1.20/1.45         (~ (v4_relat_1 @ X3 @ X4)
% 1.20/1.45          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.45          | ~ (v1_relat_1 @ X3))),
% 1.20/1.45      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.45  thf('59', plain,
% 1.20/1.45      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.45        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.20/1.45      inference('sup-', [status(thm)], ['57', '58'])).
% 1.20/1.45  thf('60', plain,
% 1.20/1.45      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.45        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.20/1.45      inference('sup-', [status(thm)], ['36', '59'])).
% 1.20/1.45  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.45      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.45  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('63', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.20/1.45      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.20/1.45  thf('64', plain,
% 1.20/1.45      (![X0 : $i, X2 : $i]:
% 1.20/1.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.20/1.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.45  thf('65', plain,
% 1.20/1.45      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.20/1.45        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.45      inference('sup-', [status(thm)], ['63', '64'])).
% 1.20/1.45  thf('66', plain,
% 1.20/1.45      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.20/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.45        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.45      inference('sup-', [status(thm)], ['35', '65'])).
% 1.20/1.45  thf('67', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.45      inference('sup+', [status(thm)], ['39', '40'])).
% 1.20/1.45  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.45      inference('simplify', [status(thm)], ['44'])).
% 1.20/1.45  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.45      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.45  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('71', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('72', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.45      inference('demod', [status(thm)], ['66', '67', '68', '69', '70', '71'])).
% 1.20/1.45  thf(t44_relat_1, axiom,
% 1.20/1.45    (![A:$i]:
% 1.20/1.45     ( ( v1_relat_1 @ A ) =>
% 1.20/1.45       ( ![B:$i]:
% 1.20/1.45         ( ( v1_relat_1 @ B ) =>
% 1.20/1.45           ( r1_tarski @
% 1.20/1.45             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.20/1.45  thf('73', plain,
% 1.20/1.45      (![X5 : $i, X6 : $i]:
% 1.20/1.45         (~ (v1_relat_1 @ X5)
% 1.20/1.45          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 1.20/1.45             (k1_relat_1 @ X6))
% 1.20/1.45          | ~ (v1_relat_1 @ X6))),
% 1.20/1.45      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.20/1.45  thf('74', plain,
% 1.20/1.45      (![X0 : $i]:
% 1.20/1.45         ((r1_tarski @ 
% 1.20/1.45           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B)
% 1.20/1.45          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.45          | ~ (v1_relat_1 @ X0))),
% 1.20/1.45      inference('sup+', [status(thm)], ['72', '73'])).
% 1.20/1.45  thf('75', plain,
% 1.20/1.45      (![X0 : $i]:
% 1.20/1.45         (~ (v1_relat_1 @ sk_C)
% 1.20/1.45          | ~ (v1_funct_1 @ sk_C)
% 1.20/1.45          | ~ (v1_relat_1 @ X0)
% 1.20/1.45          | (r1_tarski @ 
% 1.20/1.45             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B))),
% 1.20/1.45      inference('sup-', [status(thm)], ['34', '74'])).
% 1.20/1.45  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.45      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.45  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('78', plain,
% 1.20/1.45      (![X0 : $i]:
% 1.20/1.45         (~ (v1_relat_1 @ X0)
% 1.20/1.45          | (r1_tarski @ 
% 1.20/1.45             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B))),
% 1.20/1.45      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.20/1.45  thf('79', plain,
% 1.20/1.45      (![X3 : $i, X4 : $i]:
% 1.20/1.45         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.45          | (v4_relat_1 @ X3 @ X4)
% 1.20/1.45          | ~ (v1_relat_1 @ X3))),
% 1.20/1.45      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.45  thf('80', plain,
% 1.20/1.45      (![X0 : $i]:
% 1.20/1.45         (~ (v1_relat_1 @ X0)
% 1.20/1.45          | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 1.20/1.45          | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B))),
% 1.20/1.45      inference('sup-', [status(thm)], ['78', '79'])).
% 1.20/1.45  thf('81', plain,
% 1.20/1.45      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.20/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.45        | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)
% 1.20/1.45        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.45      inference('sup-', [status(thm)], ['33', '80'])).
% 1.20/1.45  thf('82', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.45      inference('sup+', [status(thm)], ['39', '40'])).
% 1.20/1.45  thf('83', plain,
% 1.20/1.45      (![X31 : $i]:
% 1.20/1.45         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 1.20/1.45          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 1.20/1.45      inference('demod', [status(thm)], ['21', '22'])).
% 1.20/1.45  thf('84', plain,
% 1.20/1.45      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.20/1.45         ((v1_relat_1 @ X18)
% 1.20/1.45          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.20/1.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.20/1.45  thf('85', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.45      inference('sup-', [status(thm)], ['83', '84'])).
% 1.20/1.45  thf('86', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.45      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.45  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.45      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.45  thf('90', plain,
% 1.20/1.45      ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)),
% 1.20/1.45      inference('demod', [status(thm)],
% 1.20/1.45                ['81', '82', '85', '86', '87', '88', '89'])).
% 1.20/1.45  thf('91', plain,
% 1.20/1.45      (![X3 : $i, X4 : $i]:
% 1.20/1.45         (~ (v4_relat_1 @ X3 @ X4)
% 1.20/1.45          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.45          | ~ (v1_relat_1 @ X3))),
% 1.20/1.45      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.45  thf('92', plain,
% 1.20/1.45      ((~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.20/1.45        | (r1_tarski @ 
% 1.20/1.45           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ sk_B))),
% 1.20/1.45      inference('sup-', [status(thm)], ['90', '91'])).
% 1.20/1.45  thf('93', plain,
% 1.20/1.45      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.20/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.45        | (r1_tarski @ 
% 1.20/1.45           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ sk_B))),
% 1.20/1.45      inference('sup-', [status(thm)], ['32', '92'])).
% 1.20/1.45  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.45      inference('sup+', [status(thm)], ['39', '40'])).
% 1.20/1.45  thf('95', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.45      inference('sup-', [status(thm)], ['83', '84'])).
% 1.20/1.45  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.45      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.45  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.45  thf('99', plain,
% 1.20/1.45      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ 
% 1.20/1.45        sk_B)),
% 1.20/1.45      inference('demod', [status(thm)], ['93', '94', '95', '96', '97', '98'])).
% 1.20/1.45  thf(t71_relat_1, axiom,
% 1.20/1.45    (![A:$i]:
% 1.20/1.45     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.20/1.45       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.20/1.45  thf('100', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 1.20/1.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.20/1.45  thf('101', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 1.20/1.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.45  thf('102', plain,
% 1.20/1.45      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 1.20/1.45      inference('demod', [status(thm)], ['100', '101'])).
% 1.20/1.45  thf(t77_relat_1, axiom,
% 1.20/1.45    (![A:$i,B:$i]:
% 1.20/1.45     ( ( v1_relat_1 @ B ) =>
% 1.20/1.45       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.20/1.45         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.20/1.45  thf('103', plain,
% 1.20/1.45      (![X12 : $i, X13 : $i]:
% 1.20/1.45         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 1.20/1.45          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 1.20/1.45          | ~ (v1_relat_1 @ X12))),
% 1.20/1.45      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.20/1.45  thf('104', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 1.20/1.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.45  thf('105', plain,
% 1.20/1.45      (![X12 : $i, X13 : $i]:
% 1.20/1.45         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 1.20/1.45          | ((k5_relat_1 @ (k6_partfun1 @ X13) @ X12) = (X12))
% 1.20/1.45          | ~ (v1_relat_1 @ X12))),
% 1.20/1.45      inference('demod', [status(thm)], ['103', '104'])).
% 1.20/1.45  thf('106', plain,
% 1.20/1.45      (![X0 : $i, X1 : $i]:
% 1.20/1.45         (~ (r1_tarski @ X0 @ X1)
% 1.20/1.45          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.20/1.45          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 1.20/1.45              = (k6_partfun1 @ X0)))),
% 1.20/1.45      inference('sup-', [status(thm)], ['102', '105'])).
% 1.20/1.45  thf('107', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.45      inference('sup-', [status(thm)], ['83', '84'])).
% 1.20/1.45  thf('108', plain,
% 1.20/1.45      (![X0 : $i, X1 : $i]:
% 1.20/1.45         (~ (r1_tarski @ X0 @ X1)
% 1.20/1.45          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 1.20/1.45              = (k6_partfun1 @ X0)))),
% 1.20/1.45      inference('demod', [status(thm)], ['106', '107'])).
% 1.20/1.45  thf('109', plain,
% 1.20/1.45      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.45         (k6_partfun1 @ 
% 1.20/1.45          (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))
% 1.20/1.45         = (k6_partfun1 @ 
% 1.20/1.45            (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))),
% 1.20/1.45      inference('sup-', [status(thm)], ['99', '108'])).
% 1.20/1.45  thf('110', plain,
% 1.20/1.45      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.45          (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))))
% 1.20/1.45          = (k6_partfun1 @ 
% 1.20/1.45             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))
% 1.20/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.20/1.45      inference('sup+', [status(thm)], ['31', '109'])).
% 1.20/1.45  thf('111', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.45      inference('sup+', [status(thm)], ['39', '40'])).
% 1.20/1.45  thf('112', plain,
% 1.20/1.45      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 1.20/1.45      inference('demod', [status(thm)], ['100', '101'])).
% 1.20/1.45  thf('113', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 1.20/1.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.20/1.45  thf('114', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 1.20/1.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.45  thf('115', plain,
% 1.20/1.45      (![X11 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 1.20/1.45      inference('demod', [status(thm)], ['113', '114'])).
% 1.20/1.45  thf(t80_relat_1, axiom,
% 1.20/1.45    (![A:$i]:
% 1.20/1.45     ( ( v1_relat_1 @ A ) =>
% 1.20/1.45       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.20/1.45  thf('116', plain,
% 1.20/1.45      (![X14 : $i]:
% 1.20/1.45         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 1.20/1.45          | ~ (v1_relat_1 @ X14))),
% 1.20/1.45      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.20/1.45  thf('117', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 1.20/1.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.46  thf('118', plain,
% 1.20/1.46      (![X14 : $i]:
% 1.20/1.46         (((k5_relat_1 @ X14 @ (k6_partfun1 @ (k2_relat_1 @ X14))) = (X14))
% 1.20/1.46          | ~ (v1_relat_1 @ X14))),
% 1.20/1.46      inference('demod', [status(thm)], ['116', '117'])).
% 1.20/1.46  thf('119', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.20/1.46            = (k6_partfun1 @ X0))
% 1.20/1.46          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.20/1.46      inference('sup+', [status(thm)], ['115', '118'])).
% 1.20/1.46  thf('120', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.46      inference('sup-', [status(thm)], ['83', '84'])).
% 1.20/1.46  thf('121', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.20/1.46           = (k6_partfun1 @ X0))),
% 1.20/1.46      inference('demod', [status(thm)], ['119', '120'])).
% 1.20/1.46  thf('122', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('124', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('125', plain,
% 1.20/1.46      (((k6_partfun1 @ sk_B)
% 1.20/1.46         = (k6_partfun1 @ 
% 1.20/1.46            (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))),
% 1.20/1.46      inference('demod', [status(thm)],
% 1.20/1.46                ['110', '111', '112', '121', '122', '123', '124'])).
% 1.20/1.46  thf('126', plain,
% 1.20/1.46      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 1.20/1.46      inference('demod', [status(thm)], ['100', '101'])).
% 1.20/1.46  thf('127', plain,
% 1.20/1.46      (((k1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.20/1.46         = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.20/1.46      inference('sup+', [status(thm)], ['125', '126'])).
% 1.20/1.46  thf('128', plain,
% 1.20/1.46      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 1.20/1.46      inference('demod', [status(thm)], ['100', '101'])).
% 1.20/1.46  thf('129', plain,
% 1.20/1.46      (((sk_B) = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.20/1.46      inference('demod', [status(thm)], ['127', '128'])).
% 1.20/1.46  thf('130', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.46      inference('simplify', [status(thm)], ['44'])).
% 1.20/1.46  thf('131', plain,
% 1.20/1.46      (![X12 : $i, X13 : $i]:
% 1.20/1.46         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 1.20/1.46          | ((k5_relat_1 @ (k6_partfun1 @ X13) @ X12) = (X12))
% 1.20/1.46          | ~ (v1_relat_1 @ X12))),
% 1.20/1.46      inference('demod', [status(thm)], ['103', '104'])).
% 1.20/1.46  thf('132', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         (~ (v1_relat_1 @ X0)
% 1.20/1.46          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.20/1.46      inference('sup-', [status(thm)], ['130', '131'])).
% 1.20/1.46  thf('133', plain,
% 1.20/1.46      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.46          (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.20/1.46          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.20/1.46        | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.20/1.46      inference('sup+', [status(thm)], ['129', '132'])).
% 1.20/1.46  thf('134', plain,
% 1.20/1.46      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.20/1.46        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.46        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.46        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.46        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.46            (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.20/1.46            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.20/1.46      inference('sup-', [status(thm)], ['30', '133'])).
% 1.20/1.46  thf('135', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.46      inference('sup+', [status(thm)], ['39', '40'])).
% 1.20/1.46  thf('136', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.46      inference('sup-', [status(thm)], ['83', '84'])).
% 1.20/1.46  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('140', plain,
% 1.20/1.46      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.46         (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.20/1.46         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.20/1.46      inference('demod', [status(thm)],
% 1.20/1.46                ['134', '135', '136', '137', '138', '139'])).
% 1.20/1.46  thf('141', plain,
% 1.20/1.46      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.46          (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.20/1.46          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.20/1.46        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.46        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.46        | ~ (v2_funct_1 @ sk_C))),
% 1.20/1.46      inference('sup+', [status(thm)], ['29', '140'])).
% 1.20/1.46  thf('142', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.46      inference('sup+', [status(thm)], ['39', '40'])).
% 1.20/1.46  thf('143', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.20/1.46           = (k6_partfun1 @ X0))),
% 1.20/1.46      inference('demod', [status(thm)], ['119', '120'])).
% 1.20/1.46  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('146', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('147', plain,
% 1.20/1.46      (((k6_partfun1 @ sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.20/1.46      inference('demod', [status(thm)],
% 1.20/1.46                ['141', '142', '143', '144', '145', '146'])).
% 1.20/1.46  thf(t55_relat_1, axiom,
% 1.20/1.46    (![A:$i]:
% 1.20/1.46     ( ( v1_relat_1 @ A ) =>
% 1.20/1.46       ( ![B:$i]:
% 1.20/1.46         ( ( v1_relat_1 @ B ) =>
% 1.20/1.46           ( ![C:$i]:
% 1.20/1.46             ( ( v1_relat_1 @ C ) =>
% 1.20/1.46               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.20/1.46                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.20/1.46  thf('148', plain,
% 1.20/1.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.20/1.46         (~ (v1_relat_1 @ X7)
% 1.20/1.46          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 1.20/1.46              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 1.20/1.46          | ~ (v1_relat_1 @ X9)
% 1.20/1.46          | ~ (v1_relat_1 @ X8))),
% 1.20/1.46      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.46  thf('149', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.46            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.20/1.46          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.46          | ~ (v1_relat_1 @ X0)
% 1.20/1.46          | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.46      inference('sup+', [status(thm)], ['147', '148'])).
% 1.20/1.46  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('151', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.46            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.20/1.46          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.46          | ~ (v1_relat_1 @ X0))),
% 1.20/1.46      inference('demod', [status(thm)], ['149', '150'])).
% 1.20/1.46  thf('152', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         (~ (v1_relat_1 @ sk_C)
% 1.20/1.46          | ~ (v1_funct_1 @ sk_C)
% 1.20/1.46          | ~ (v1_relat_1 @ X0)
% 1.20/1.46          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.46              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.20/1.46      inference('sup-', [status(thm)], ['26', '151'])).
% 1.20/1.46  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('155', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         (~ (v1_relat_1 @ X0)
% 1.20/1.46          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.46              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.20/1.46      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.20/1.46  thf('156', plain,
% 1.20/1.46      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.20/1.46          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.20/1.46        | ~ (v1_relat_1 @ sk_D))),
% 1.20/1.46      inference('sup+', [status(thm)], ['25', '155'])).
% 1.20/1.46  thf('157', plain,
% 1.20/1.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf(cc2_relset_1, axiom,
% 1.20/1.46    (![A:$i,B:$i,C:$i]:
% 1.20/1.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.20/1.46  thf('158', plain,
% 1.20/1.46      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.20/1.46         ((v4_relat_1 @ X21 @ X22)
% 1.20/1.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.20/1.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.46  thf('159', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.20/1.46      inference('sup-', [status(thm)], ['157', '158'])).
% 1.20/1.46  thf('160', plain,
% 1.20/1.46      (![X3 : $i, X4 : $i]:
% 1.20/1.46         (~ (v4_relat_1 @ X3 @ X4)
% 1.20/1.46          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.46          | ~ (v1_relat_1 @ X3))),
% 1.20/1.46      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.46  thf('161', plain,
% 1.20/1.46      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.20/1.46      inference('sup-', [status(thm)], ['159', '160'])).
% 1.20/1.46  thf('162', plain,
% 1.20/1.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('163', plain,
% 1.20/1.46      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.20/1.46         ((v1_relat_1 @ X18)
% 1.20/1.46          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.20/1.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.20/1.46  thf('164', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.46      inference('sup-', [status(thm)], ['162', '163'])).
% 1.20/1.46  thf('165', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.20/1.46      inference('demod', [status(thm)], ['161', '164'])).
% 1.20/1.46  thf('166', plain,
% 1.20/1.46      (![X12 : $i, X13 : $i]:
% 1.20/1.46         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 1.20/1.46          | ((k5_relat_1 @ (k6_partfun1 @ X13) @ X12) = (X12))
% 1.20/1.46          | ~ (v1_relat_1 @ X12))),
% 1.20/1.46      inference('demod', [status(thm)], ['103', '104'])).
% 1.20/1.46  thf('167', plain,
% 1.20/1.46      ((~ (v1_relat_1 @ sk_D)
% 1.20/1.46        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 1.20/1.46      inference('sup-', [status(thm)], ['165', '166'])).
% 1.20/1.46  thf('168', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.46      inference('sup-', [status(thm)], ['162', '163'])).
% 1.20/1.46  thf('169', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.20/1.46      inference('demod', [status(thm)], ['167', '168'])).
% 1.20/1.46  thf('170', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.46      inference('sup-', [status(thm)], ['162', '163'])).
% 1.20/1.46  thf('171', plain,
% 1.20/1.46      (((sk_D) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.20/1.46      inference('demod', [status(thm)], ['156', '169', '170'])).
% 1.20/1.46  thf('172', plain,
% 1.20/1.46      (![X15 : $i]:
% 1.20/1.46         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.20/1.46          | ~ (v1_funct_1 @ X15)
% 1.20/1.46          | ~ (v1_relat_1 @ X15))),
% 1.20/1.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.46  thf('173', plain,
% 1.20/1.46      (![X17 : $i]:
% 1.20/1.46         (~ (v2_funct_1 @ X17)
% 1.20/1.46          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 1.20/1.46              = (k6_relat_1 @ (k1_relat_1 @ X17)))
% 1.20/1.46          | ~ (v1_funct_1 @ X17)
% 1.20/1.46          | ~ (v1_relat_1 @ X17))),
% 1.20/1.46      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.46  thf('174', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 1.20/1.46      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.46  thf('175', plain,
% 1.20/1.46      (![X17 : $i]:
% 1.20/1.46         (~ (v2_funct_1 @ X17)
% 1.20/1.46          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 1.20/1.46              = (k6_partfun1 @ (k1_relat_1 @ X17)))
% 1.20/1.46          | ~ (v1_funct_1 @ X17)
% 1.20/1.46          | ~ (v1_relat_1 @ X17))),
% 1.20/1.46      inference('demod', [status(thm)], ['173', '174'])).
% 1.20/1.46  thf('176', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         (~ (v1_relat_1 @ X0)
% 1.20/1.46          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.46              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.20/1.46      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.20/1.46  thf('177', plain,
% 1.20/1.46      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.20/1.46          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.46             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.20/1.46        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.46        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.46        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.46        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.46      inference('sup+', [status(thm)], ['175', '176'])).
% 1.20/1.46  thf('178', plain,
% 1.20/1.46      (![X15 : $i]:
% 1.20/1.46         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.20/1.46          | ~ (v1_funct_1 @ X15)
% 1.20/1.46          | ~ (v1_relat_1 @ X15))),
% 1.20/1.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.46  thf('179', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.46      inference('demod', [status(thm)], ['66', '67', '68', '69', '70', '71'])).
% 1.20/1.46  thf('180', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         (~ (v1_relat_1 @ X0)
% 1.20/1.46          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.20/1.46      inference('sup-', [status(thm)], ['130', '131'])).
% 1.20/1.46  thf('181', plain,
% 1.20/1.46      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.20/1.46          = (k2_funct_1 @ sk_C))
% 1.20/1.46        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.46      inference('sup+', [status(thm)], ['179', '180'])).
% 1.20/1.46  thf('182', plain,
% 1.20/1.46      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.46        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.46        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.20/1.46            = (k2_funct_1 @ sk_C)))),
% 1.20/1.46      inference('sup-', [status(thm)], ['178', '181'])).
% 1.20/1.46  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('185', plain,
% 1.20/1.46      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.20/1.46         = (k2_funct_1 @ sk_C))),
% 1.20/1.46      inference('demod', [status(thm)], ['182', '183', '184'])).
% 1.20/1.46  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('189', plain,
% 1.20/1.46      ((((k2_funct_1 @ sk_C)
% 1.20/1.46          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.46             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.20/1.46        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.46      inference('demod', [status(thm)], ['177', '185', '186', '187', '188'])).
% 1.20/1.46  thf('190', plain,
% 1.20/1.46      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.46        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.46        | ((k2_funct_1 @ sk_C)
% 1.20/1.46            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.46               (k6_partfun1 @ (k1_relat_1 @ sk_C)))))),
% 1.20/1.46      inference('sup-', [status(thm)], ['172', '189'])).
% 1.20/1.46  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('192', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('193', plain,
% 1.20/1.46      (((k2_funct_1 @ sk_C)
% 1.20/1.46         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.46            (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.20/1.46      inference('demod', [status(thm)], ['190', '191', '192'])).
% 1.20/1.46  thf('194', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.20/1.46      inference('demod', [status(thm)], ['167', '168'])).
% 1.20/1.46  thf('195', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.46      inference('sup+', [status(thm)], ['39', '40'])).
% 1.20/1.46  thf('196', plain,
% 1.20/1.46      (![X14 : $i]:
% 1.20/1.46         (((k5_relat_1 @ X14 @ (k6_partfun1 @ (k2_relat_1 @ X14))) = (X14))
% 1.20/1.46          | ~ (v1_relat_1 @ X14))),
% 1.20/1.46      inference('demod', [status(thm)], ['116', '117'])).
% 1.20/1.46  thf('197', plain,
% 1.20/1.46      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 1.20/1.46        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.46      inference('sup+', [status(thm)], ['195', '196'])).
% 1.20/1.46  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('199', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.20/1.46      inference('demod', [status(thm)], ['197', '198'])).
% 1.20/1.46  thf('200', plain,
% 1.20/1.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.20/1.46         (~ (v1_relat_1 @ X7)
% 1.20/1.46          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 1.20/1.46              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 1.20/1.46          | ~ (v1_relat_1 @ X9)
% 1.20/1.46          | ~ (v1_relat_1 @ X8))),
% 1.20/1.46      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.46  thf('201', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         (((k5_relat_1 @ sk_C @ X0)
% 1.20/1.46            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 1.20/1.46          | ~ (v1_relat_1 @ sk_C)
% 1.20/1.46          | ~ (v1_relat_1 @ X0)
% 1.20/1.46          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.20/1.46      inference('sup+', [status(thm)], ['199', '200'])).
% 1.20/1.46  thf('202', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('203', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.46      inference('sup-', [status(thm)], ['83', '84'])).
% 1.20/1.46  thf('204', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         (((k5_relat_1 @ sk_C @ X0)
% 1.20/1.46            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 1.20/1.46          | ~ (v1_relat_1 @ X0))),
% 1.20/1.46      inference('demod', [status(thm)], ['201', '202', '203'])).
% 1.20/1.46  thf('205', plain,
% 1.20/1.46      (![X5 : $i, X6 : $i]:
% 1.20/1.46         (~ (v1_relat_1 @ X5)
% 1.20/1.46          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 1.20/1.46             (k1_relat_1 @ X6))
% 1.20/1.46          | ~ (v1_relat_1 @ X6))),
% 1.20/1.46      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.20/1.46  thf('206', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ X0)) @ 
% 1.20/1.46           (k1_relat_1 @ sk_C))
% 1.20/1.46          | ~ (v1_relat_1 @ X0)
% 1.20/1.46          | ~ (v1_relat_1 @ sk_C)
% 1.20/1.46          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))),
% 1.20/1.46      inference('sup+', [status(thm)], ['204', '205'])).
% 1.20/1.46  thf('207', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('208', plain,
% 1.20/1.46      (![X0 : $i]:
% 1.20/1.46         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ X0)) @ 
% 1.20/1.46           (k1_relat_1 @ sk_C))
% 1.20/1.46          | ~ (v1_relat_1 @ X0)
% 1.20/1.46          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))),
% 1.20/1.46      inference('demod', [status(thm)], ['206', '207'])).
% 1.20/1.46  thf('209', plain,
% 1.20/1.46      ((~ (v1_relat_1 @ sk_D)
% 1.20/1.46        | ~ (v1_relat_1 @ sk_D)
% 1.20/1.46        | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 1.20/1.46           (k1_relat_1 @ sk_C)))),
% 1.20/1.46      inference('sup-', [status(thm)], ['194', '208'])).
% 1.20/1.46  thf('210', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.46      inference('sup-', [status(thm)], ['162', '163'])).
% 1.20/1.46  thf('211', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.46      inference('sup-', [status(thm)], ['162', '163'])).
% 1.20/1.46  thf('212', plain,
% 1.20/1.46      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 1.20/1.46        (k1_relat_1 @ sk_C))),
% 1.20/1.46      inference('demod', [status(thm)], ['209', '210', '211'])).
% 1.20/1.46  thf('213', plain,
% 1.20/1.46      (![X0 : $i, X2 : $i]:
% 1.20/1.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.20/1.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.46  thf('214', plain,
% 1.20/1.46      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 1.20/1.46           (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.20/1.46        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 1.20/1.46      inference('sup-', [status(thm)], ['212', '213'])).
% 1.20/1.46  thf('215', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.46      inference('demod', [status(thm)], ['6', '7', '24'])).
% 1.20/1.46  thf('216', plain,
% 1.20/1.46      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 1.20/1.46      inference('demod', [status(thm)], ['100', '101'])).
% 1.20/1.46  thf('217', plain,
% 1.20/1.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('218', plain,
% 1.20/1.46      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.20/1.46         ((v4_relat_1 @ X21 @ X22)
% 1.20/1.46          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.20/1.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.46  thf('219', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.20/1.46      inference('sup-', [status(thm)], ['217', '218'])).
% 1.20/1.46  thf('220', plain,
% 1.20/1.46      (![X3 : $i, X4 : $i]:
% 1.20/1.46         (~ (v4_relat_1 @ X3 @ X4)
% 1.20/1.46          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.46          | ~ (v1_relat_1 @ X3))),
% 1.20/1.46      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.46  thf('221', plain,
% 1.20/1.46      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.20/1.46      inference('sup-', [status(thm)], ['219', '220'])).
% 1.20/1.46  thf('222', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.46      inference('sup-', [status(thm)], ['52', '53'])).
% 1.20/1.46  thf('223', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.20/1.46      inference('demod', [status(thm)], ['221', '222'])).
% 1.20/1.46  thf('224', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.46      inference('demod', [status(thm)], ['6', '7', '24'])).
% 1.20/1.46  thf('225', plain,
% 1.20/1.46      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 1.20/1.46      inference('demod', [status(thm)], ['100', '101'])).
% 1.20/1.46  thf('226', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.20/1.46      inference('demod', [status(thm)],
% 1.20/1.46                ['214', '215', '216', '223', '224', '225'])).
% 1.20/1.46  thf('227', plain,
% 1.20/1.46      (((k2_funct_1 @ sk_C)
% 1.20/1.46         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.20/1.46      inference('demod', [status(thm)], ['193', '226'])).
% 1.20/1.46  thf('228', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 1.20/1.46      inference('sup+', [status(thm)], ['171', '227'])).
% 1.20/1.46  thf('229', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.20/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.46  thf('230', plain, ($false),
% 1.20/1.46      inference('simplify_reflect-', [status(thm)], ['228', '229'])).
% 1.20/1.46  
% 1.20/1.46  % SZS output end Refutation
% 1.20/1.46  
% 1.30/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
