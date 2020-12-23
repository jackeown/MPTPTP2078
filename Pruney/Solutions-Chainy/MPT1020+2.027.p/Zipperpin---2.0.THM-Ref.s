%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VxbQfD0W20

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:04 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  209 (1250 expanded)
%              Number of leaves         :   45 ( 379 expanded)
%              Depth                    :   21
%              Number of atoms          : 1829 (30906 expanded)
%              Number of equality atoms :  131 ( 481 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_funct_2 @ X41 @ X40 )
        = ( k2_funct_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X41 @ X41 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X41 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('11',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('20',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('31',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('35',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('36',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
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

thf('39',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( X47
        = ( k2_funct_1 @ X50 ) )
      | ~ ( r2_relset_1 @ X49 @ X49 @ ( k1_partfun1 @ X49 @ X48 @ X48 @ X49 @ X50 @ X47 ) @ ( k6_partfun1 @ X49 ) )
      | ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X49 @ X48 @ X50 )
       != X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('47',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('58',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('65',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('69',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['63','66','69'])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['55','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('74',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','49','50','51','52','71','77'])).

thf('79',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('81',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('84',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','84'])).

thf('87',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('90',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('101',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['95','98','101'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('104',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['96','97'])).

thf('106',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','84'])).

thf('108',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['63','66','69'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('112',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('114',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','84'])).

thf('116',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['116'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('118',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('119',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('120',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['118','119'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('121',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('122',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('123',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X2 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('124',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ X3 @ ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('125',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('126',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ X3 @ ( k6_partfun1 @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('128',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('129',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('130',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['127','130'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('132',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X7 @ X6 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('133',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('134',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X7 @ X6 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k6_partfun1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('137',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('138',plain,(
    ! [X1: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('140',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('141',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('142',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X2: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X2 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('144',plain,(
    ! [X1: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('145',plain,(
    ! [X5: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('146',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( X0 != X0 )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['135','138','139','142','143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ~ ( v2_funct_1 @ k1_xboole_0 )
    | ( ( k6_partfun1 @ k1_xboole_0 )
      = ( k2_funct_1 @ ( k6_partfun1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['120','148'])).

thf('150',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['118','119'])).

thf('151',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['118','119'])).

thf('152',plain,
    ( ~ ( v2_funct_1 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('154',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['116'])).

thf('155',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['152','155'])).

thf('157',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['118','119'])).

thf('158',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('159',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('161',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    $false ),
    inference(demod,[status(thm)],['87','109','117','156','161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VxbQfD0W20
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:08:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.92/1.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.92/1.11  % Solved by: fo/fo7.sh
% 0.92/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.11  % done 1408 iterations in 0.656s
% 0.92/1.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.92/1.11  % SZS output start Refutation
% 0.92/1.11  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.92/1.11  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.92/1.11  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.92/1.11  thf(sk_C_type, type, sk_C: $i).
% 0.92/1.11  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.92/1.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.92/1.11  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.92/1.11  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.92/1.11  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.92/1.11  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.92/1.11  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.92/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.11  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.92/1.11  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.92/1.11  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.92/1.11  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.92/1.11  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.92/1.11  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.92/1.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.92/1.11  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.92/1.11  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.92/1.11  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.92/1.11  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.92/1.11  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.92/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.11  thf(t87_funct_2, conjecture,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.92/1.11         ( v3_funct_2 @ B @ A @ A ) & 
% 0.92/1.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.92/1.11       ( ![C:$i]:
% 0.92/1.11         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.92/1.11             ( v3_funct_2 @ C @ A @ A ) & 
% 0.92/1.11             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.92/1.11           ( ( r2_relset_1 @
% 0.92/1.11               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.92/1.11               ( k6_partfun1 @ A ) ) =>
% 0.92/1.11             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.92/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.11    (~( ![A:$i,B:$i]:
% 0.92/1.11        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.92/1.11            ( v3_funct_2 @ B @ A @ A ) & 
% 0.92/1.11            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.92/1.11          ( ![C:$i]:
% 0.92/1.11            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.92/1.11                ( v3_funct_2 @ C @ A @ A ) & 
% 0.92/1.11                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.92/1.11              ( ( r2_relset_1 @
% 0.92/1.11                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.92/1.11                  ( k6_partfun1 @ A ) ) =>
% 0.92/1.11                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.92/1.11    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.92/1.11  thf('0', plain,
% 0.92/1.11      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('1', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(redefinition_k2_funct_2, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.92/1.11         ( v3_funct_2 @ B @ A @ A ) & 
% 0.92/1.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.92/1.11       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.92/1.11  thf('2', plain,
% 0.92/1.11      (![X40 : $i, X41 : $i]:
% 0.92/1.11         (((k2_funct_2 @ X41 @ X40) = (k2_funct_1 @ X40))
% 0.92/1.11          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))
% 0.92/1.11          | ~ (v3_funct_2 @ X40 @ X41 @ X41)
% 0.92/1.11          | ~ (v1_funct_2 @ X40 @ X41 @ X41)
% 0.92/1.11          | ~ (v1_funct_1 @ X40))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.92/1.11  thf('3', plain,
% 0.92/1.11      ((~ (v1_funct_1 @ sk_B)
% 0.92/1.11        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.92/1.11        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.92/1.11        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['1', '2'])).
% 0.92/1.11  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.92/1.11      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.92/1.11  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.92/1.11      inference('demod', [status(thm)], ['0', '7'])).
% 0.92/1.11  thf('9', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('10', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(redefinition_k1_partfun1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.92/1.11     ( ( ( v1_funct_1 @ E ) & 
% 0.92/1.11         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.92/1.11         ( v1_funct_1 @ F ) & 
% 0.92/1.11         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.92/1.11       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.92/1.11  thf('11', plain,
% 0.92/1.11      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.92/1.11         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.92/1.11          | ~ (v1_funct_1 @ X34)
% 0.92/1.11          | ~ (v1_funct_1 @ X37)
% 0.92/1.11          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.92/1.11          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 0.92/1.11              = (k5_relat_1 @ X34 @ X37)))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.92/1.11  thf('12', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.11         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.92/1.11            = (k5_relat_1 @ sk_B @ X0))
% 0.92/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.92/1.11          | ~ (v1_funct_1 @ X0)
% 0.92/1.11          | ~ (v1_funct_1 @ sk_B))),
% 0.92/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.92/1.11  thf('13', plain, ((v1_funct_1 @ sk_B)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('14', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.11         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.92/1.11            = (k5_relat_1 @ sk_B @ X0))
% 0.92/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.92/1.11          | ~ (v1_funct_1 @ X0))),
% 0.92/1.11      inference('demod', [status(thm)], ['12', '13'])).
% 0.92/1.11  thf('15', plain,
% 0.92/1.11      ((~ (v1_funct_1 @ sk_C)
% 0.92/1.11        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.92/1.11            = (k5_relat_1 @ sk_B @ sk_C)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['9', '14'])).
% 0.92/1.11  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('17', plain,
% 0.92/1.11      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.92/1.11         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.92/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.92/1.11  thf('18', plain,
% 0.92/1.11      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.92/1.11        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.92/1.11        (k6_partfun1 @ sk_A))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('19', plain,
% 0.92/1.11      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.92/1.11         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.92/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.92/1.11  thf('20', plain,
% 0.92/1.11      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C) @ 
% 0.92/1.11        (k6_partfun1 @ sk_A))),
% 0.92/1.11      inference('demod', [status(thm)], ['18', '19'])).
% 0.92/1.11  thf('21', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('22', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(dt_k1_partfun1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.92/1.11     ( ( ( v1_funct_1 @ E ) & 
% 0.92/1.11         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.92/1.11         ( v1_funct_1 @ F ) & 
% 0.92/1.11         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.92/1.11       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.92/1.11         ( m1_subset_1 @
% 0.92/1.11           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.92/1.11           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.92/1.11  thf('23', plain,
% 0.92/1.11      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.92/1.11         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.92/1.11          | ~ (v1_funct_1 @ X26)
% 0.92/1.11          | ~ (v1_funct_1 @ X29)
% 0.92/1.11          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.92/1.11          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 0.92/1.11             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 0.92/1.11      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.92/1.11  thf('24', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.11         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.92/1.11           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.92/1.11          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.92/1.11          | ~ (v1_funct_1 @ X1)
% 0.92/1.11          | ~ (v1_funct_1 @ sk_B))),
% 0.92/1.11      inference('sup-', [status(thm)], ['22', '23'])).
% 0.92/1.11  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('26', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.11         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.92/1.11           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.92/1.11          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.92/1.11          | ~ (v1_funct_1 @ X1))),
% 0.92/1.11      inference('demod', [status(thm)], ['24', '25'])).
% 0.92/1.11  thf('27', plain,
% 0.92/1.11      ((~ (v1_funct_1 @ sk_C)
% 0.92/1.11        | (m1_subset_1 @ 
% 0.92/1.11           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.92/1.11           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['21', '26'])).
% 0.92/1.11  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('29', plain,
% 0.92/1.11      ((m1_subset_1 @ 
% 0.92/1.11        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.92/1.11        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('demod', [status(thm)], ['27', '28'])).
% 0.92/1.11  thf('30', plain,
% 0.92/1.11      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.92/1.11         = (k5_relat_1 @ sk_B @ sk_C))),
% 0.92/1.11      inference('demod', [status(thm)], ['15', '16'])).
% 0.92/1.11  thf('31', plain,
% 0.92/1.11      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ sk_C) @ 
% 0.92/1.11        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('demod', [status(thm)], ['29', '30'])).
% 0.92/1.11  thf(redefinition_r2_relset_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i,D:$i]:
% 0.92/1.11     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.92/1.11         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.11       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.92/1.11  thf('32', plain,
% 0.92/1.11      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.11         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.92/1.11          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.92/1.11          | ((X17) = (X20))
% 0.92/1.11          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.92/1.11  thf('33', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C) @ X0)
% 0.92/1.11          | ((k5_relat_1 @ sk_B @ sk_C) = (X0))
% 0.92/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['31', '32'])).
% 0.92/1.11  thf('34', plain,
% 0.92/1.11      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.92/1.11           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.92/1.11        | ((k5_relat_1 @ sk_B @ sk_C) = (k6_partfun1 @ sk_A)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['20', '33'])).
% 0.92/1.11  thf(dt_k6_partfun1, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( m1_subset_1 @
% 0.92/1.11         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.92/1.11       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.92/1.11  thf('35', plain,
% 0.92/1.11      (![X33 : $i]:
% 0.92/1.11         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 0.92/1.11          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.92/1.11      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.92/1.11  thf('36', plain, (((k5_relat_1 @ sk_B @ sk_C) = (k6_partfun1 @ sk_A))),
% 0.92/1.11      inference('demod', [status(thm)], ['34', '35'])).
% 0.92/1.11  thf('37', plain,
% 0.92/1.11      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.92/1.11         = (k6_partfun1 @ sk_A))),
% 0.92/1.11      inference('demod', [status(thm)], ['17', '36'])).
% 0.92/1.11  thf('38', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(t36_funct_2, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.92/1.11         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.11       ( ![D:$i]:
% 0.92/1.11         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.92/1.11             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.92/1.11           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.92/1.11               ( r2_relset_1 @
% 0.92/1.11                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.92/1.11                 ( k6_partfun1 @ A ) ) & 
% 0.92/1.11               ( v2_funct_1 @ C ) ) =>
% 0.92/1.11             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.92/1.11               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.92/1.11  thf('39', plain,
% 0.92/1.11      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.92/1.11         (~ (v1_funct_1 @ X47)
% 0.92/1.11          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 0.92/1.11          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.92/1.11          | ((X47) = (k2_funct_1 @ X50))
% 0.92/1.11          | ~ (r2_relset_1 @ X49 @ X49 @ 
% 0.92/1.11               (k1_partfun1 @ X49 @ X48 @ X48 @ X49 @ X50 @ X47) @ 
% 0.92/1.11               (k6_partfun1 @ X49))
% 0.92/1.11          | ((X48) = (k1_xboole_0))
% 0.92/1.11          | ((X49) = (k1_xboole_0))
% 0.92/1.11          | ~ (v2_funct_1 @ X50)
% 0.92/1.11          | ((k2_relset_1 @ X49 @ X48 @ X50) != (X48))
% 0.92/1.11          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.92/1.11          | ~ (v1_funct_2 @ X50 @ X49 @ X48)
% 0.92/1.11          | ~ (v1_funct_1 @ X50))),
% 0.92/1.11      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.92/1.11  thf('40', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (v1_funct_1 @ X0)
% 0.92/1.11          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.92/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.92/1.11          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.92/1.11          | ~ (v2_funct_1 @ X0)
% 0.92/1.11          | ((sk_A) = (k1_xboole_0))
% 0.92/1.11          | ((sk_A) = (k1_xboole_0))
% 0.92/1.11          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.92/1.11               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.92/1.11               (k6_partfun1 @ sk_A))
% 0.92/1.11          | ((sk_C) = (k2_funct_1 @ X0))
% 0.92/1.11          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.92/1.11          | ~ (v1_funct_1 @ sk_C))),
% 0.92/1.11      inference('sup-', [status(thm)], ['38', '39'])).
% 0.92/1.11  thf('41', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('43', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (v1_funct_1 @ X0)
% 0.92/1.11          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.92/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.92/1.11          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.92/1.11          | ~ (v2_funct_1 @ X0)
% 0.92/1.11          | ((sk_A) = (k1_xboole_0))
% 0.92/1.11          | ((sk_A) = (k1_xboole_0))
% 0.92/1.11          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.92/1.11               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.92/1.11               (k6_partfun1 @ sk_A))
% 0.92/1.11          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.92/1.11  thf('44', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((sk_C) = (k2_funct_1 @ X0))
% 0.92/1.11          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.92/1.11               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.92/1.11               (k6_partfun1 @ sk_A))
% 0.92/1.11          | ((sk_A) = (k1_xboole_0))
% 0.92/1.11          | ~ (v2_funct_1 @ X0)
% 0.92/1.11          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.92/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.92/1.11          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.92/1.11          | ~ (v1_funct_1 @ X0))),
% 0.92/1.11      inference('simplify', [status(thm)], ['43'])).
% 0.92/1.11  thf('45', plain,
% 0.92/1.11      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.92/1.11           (k6_partfun1 @ sk_A))
% 0.92/1.11        | ~ (v1_funct_1 @ sk_B)
% 0.92/1.11        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.92/1.11        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.92/1.11        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.92/1.11        | ~ (v2_funct_1 @ sk_B)
% 0.92/1.11        | ((sk_A) = (k1_xboole_0))
% 0.92/1.11        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['37', '44'])).
% 0.92/1.11  thf('46', plain,
% 0.92/1.11      (![X33 : $i]:
% 0.92/1.11         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 0.92/1.11          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.92/1.11      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.92/1.11  thf('47', plain,
% 0.92/1.11      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.11         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.92/1.11          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.92/1.11          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 0.92/1.11          | ((X17) != (X20)))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.92/1.11  thf('48', plain,
% 0.92/1.11      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.11         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.92/1.11          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.92/1.11      inference('simplify', [status(thm)], ['47'])).
% 0.92/1.11  thf('49', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['46', '48'])).
% 0.92/1.11  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('51', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('52', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('53', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(redefinition_k2_relset_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.92/1.11       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.92/1.11  thf('54', plain,
% 0.92/1.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.92/1.11         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.92/1.11          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.92/1.11  thf('55', plain,
% 0.92/1.11      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.92/1.11      inference('sup-', [status(thm)], ['53', '54'])).
% 0.92/1.11  thf('56', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(cc2_funct_2, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.92/1.11       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.92/1.11         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.92/1.11  thf('57', plain,
% 0.92/1.11      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.92/1.11         (~ (v1_funct_1 @ X21)
% 0.92/1.11          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.92/1.11          | (v2_funct_2 @ X21 @ X23)
% 0.92/1.11          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.92/1.11      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.92/1.11  thf('58', plain,
% 0.92/1.11      (((v2_funct_2 @ sk_B @ sk_A)
% 0.92/1.11        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.92/1.11        | ~ (v1_funct_1 @ sk_B))),
% 0.92/1.11      inference('sup-', [status(thm)], ['56', '57'])).
% 0.92/1.11  thf('59', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('61', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.92/1.11      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.92/1.11  thf(d3_funct_2, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.92/1.11       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.92/1.11  thf('62', plain,
% 0.92/1.11      (![X24 : $i, X25 : $i]:
% 0.92/1.11         (~ (v2_funct_2 @ X25 @ X24)
% 0.92/1.11          | ((k2_relat_1 @ X25) = (X24))
% 0.92/1.11          | ~ (v5_relat_1 @ X25 @ X24)
% 0.92/1.11          | ~ (v1_relat_1 @ X25))),
% 0.92/1.11      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.92/1.11  thf('63', plain,
% 0.92/1.11      ((~ (v1_relat_1 @ sk_B)
% 0.92/1.11        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.92/1.11        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['61', '62'])).
% 0.92/1.11  thf('64', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(cc1_relset_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.92/1.11       ( v1_relat_1 @ C ) ))).
% 0.92/1.11  thf('65', plain,
% 0.92/1.11      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.92/1.11         ((v1_relat_1 @ X8)
% 0.92/1.11          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.92/1.11      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.92/1.11  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 0.92/1.11      inference('sup-', [status(thm)], ['64', '65'])).
% 0.92/1.11  thf('67', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(cc2_relset_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.92/1.11       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.92/1.11  thf('68', plain,
% 0.92/1.11      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.92/1.11         ((v5_relat_1 @ X11 @ X13)
% 0.92/1.11          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.92/1.11      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.92/1.11  thf('69', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.92/1.11      inference('sup-', [status(thm)], ['67', '68'])).
% 0.92/1.11  thf('70', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.92/1.11      inference('demod', [status(thm)], ['63', '66', '69'])).
% 0.92/1.11  thf('71', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.92/1.11      inference('demod', [status(thm)], ['55', '70'])).
% 0.92/1.11  thf('72', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('73', plain,
% 0.92/1.11      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.92/1.11         (~ (v1_funct_1 @ X21)
% 0.92/1.11          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.92/1.11          | (v2_funct_1 @ X21)
% 0.92/1.11          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.92/1.11      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.92/1.11  thf('74', plain,
% 0.92/1.11      (((v2_funct_1 @ sk_B)
% 0.92/1.11        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.92/1.11        | ~ (v1_funct_1 @ sk_B))),
% 0.92/1.11      inference('sup-', [status(thm)], ['72', '73'])).
% 0.92/1.11  thf('75', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('77', plain, ((v2_funct_1 @ sk_B)),
% 0.92/1.11      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.92/1.11  thf('78', plain,
% 0.92/1.11      ((((sk_A) != (sk_A))
% 0.92/1.11        | ((sk_A) = (k1_xboole_0))
% 0.92/1.11        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.92/1.11      inference('demod', [status(thm)],
% 0.92/1.11                ['45', '49', '50', '51', '52', '71', '77'])).
% 0.92/1.11  thf('79', plain,
% 0.92/1.11      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.92/1.11      inference('simplify', [status(thm)], ['78'])).
% 0.92/1.11  thf('80', plain,
% 0.92/1.11      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.92/1.11      inference('demod', [status(thm)], ['0', '7'])).
% 0.92/1.11  thf('81', plain,
% 0.92/1.11      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['79', '80'])).
% 0.92/1.11  thf('82', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('83', plain,
% 0.92/1.11      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.11         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.92/1.11          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.92/1.11      inference('simplify', [status(thm)], ['47'])).
% 0.92/1.11  thf('84', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.92/1.11      inference('sup-', [status(thm)], ['82', '83'])).
% 0.92/1.11  thf('85', plain, (((sk_A) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['81', '84'])).
% 0.92/1.11  thf('86', plain, (((sk_A) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['81', '84'])).
% 0.92/1.11  thf('87', plain,
% 0.92/1.11      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.92/1.11      inference('demod', [status(thm)], ['8', '85', '86'])).
% 0.92/1.11  thf('88', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('89', plain,
% 0.92/1.11      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.92/1.11         (~ (v1_funct_1 @ X21)
% 0.92/1.11          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.92/1.11          | (v2_funct_2 @ X21 @ X23)
% 0.92/1.11          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.92/1.11      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.92/1.11  thf('90', plain,
% 0.92/1.11      (((v2_funct_2 @ sk_C @ sk_A)
% 0.92/1.11        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.92/1.11        | ~ (v1_funct_1 @ sk_C))),
% 0.92/1.11      inference('sup-', [status(thm)], ['88', '89'])).
% 0.92/1.11  thf('91', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('93', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.92/1.11      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.92/1.11  thf('94', plain,
% 0.92/1.11      (![X24 : $i, X25 : $i]:
% 0.92/1.11         (~ (v2_funct_2 @ X25 @ X24)
% 0.92/1.11          | ((k2_relat_1 @ X25) = (X24))
% 0.92/1.11          | ~ (v5_relat_1 @ X25 @ X24)
% 0.92/1.11          | ~ (v1_relat_1 @ X25))),
% 0.92/1.11      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.92/1.11  thf('95', plain,
% 0.92/1.11      ((~ (v1_relat_1 @ sk_C)
% 0.92/1.11        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.92/1.11        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['93', '94'])).
% 0.92/1.11  thf('96', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('97', plain,
% 0.92/1.11      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.92/1.11         ((v1_relat_1 @ X8)
% 0.92/1.11          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.92/1.11      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.92/1.11  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 0.92/1.11      inference('sup-', [status(thm)], ['96', '97'])).
% 0.92/1.11  thf('99', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('100', plain,
% 0.92/1.11      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.92/1.11         ((v5_relat_1 @ X11 @ X13)
% 0.92/1.11          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.92/1.11      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.92/1.11  thf('101', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.92/1.11      inference('sup-', [status(thm)], ['99', '100'])).
% 0.92/1.11  thf('102', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.92/1.11      inference('demod', [status(thm)], ['95', '98', '101'])).
% 0.92/1.11  thf(t64_relat_1, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( v1_relat_1 @ A ) =>
% 0.92/1.11       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.92/1.11           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.92/1.11         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.92/1.11  thf('103', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.92/1.11          | ((X0) = (k1_xboole_0))
% 0.92/1.11          | ~ (v1_relat_1 @ X0))),
% 0.92/1.11      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.92/1.11  thf('104', plain,
% 0.92/1.11      ((((sk_A) != (k1_xboole_0))
% 0.92/1.11        | ~ (v1_relat_1 @ sk_C)
% 0.92/1.11        | ((sk_C) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['102', '103'])).
% 0.92/1.11  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 0.92/1.11      inference('sup-', [status(thm)], ['96', '97'])).
% 0.92/1.11  thf('106', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['104', '105'])).
% 0.92/1.11  thf('107', plain, (((sk_A) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['81', '84'])).
% 0.92/1.11  thf('108', plain,
% 0.92/1.11      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['106', '107'])).
% 0.92/1.11  thf('109', plain, (((sk_C) = (k1_xboole_0))),
% 0.92/1.11      inference('simplify', [status(thm)], ['108'])).
% 0.92/1.11  thf('110', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.92/1.11      inference('demod', [status(thm)], ['63', '66', '69'])).
% 0.92/1.11  thf('111', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.92/1.11          | ((X0) = (k1_xboole_0))
% 0.92/1.11          | ~ (v1_relat_1 @ X0))),
% 0.92/1.11      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.92/1.11  thf('112', plain,
% 0.92/1.11      ((((sk_A) != (k1_xboole_0))
% 0.92/1.11        | ~ (v1_relat_1 @ sk_B)
% 0.92/1.11        | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['110', '111'])).
% 0.92/1.11  thf('113', plain, ((v1_relat_1 @ sk_B)),
% 0.92/1.11      inference('sup-', [status(thm)], ['64', '65'])).
% 0.92/1.11  thf('114', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['112', '113'])).
% 0.92/1.11  thf('115', plain, (((sk_A) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['81', '84'])).
% 0.92/1.11  thf('116', plain,
% 0.92/1.11      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['114', '115'])).
% 0.92/1.11  thf('117', plain, (((sk_B) = (k1_xboole_0))),
% 0.92/1.11      inference('simplify', [status(thm)], ['116'])).
% 0.92/1.11  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.92/1.11  thf('118', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.11      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.92/1.11  thf(redefinition_k6_partfun1, axiom,
% 0.92/1.11    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.92/1.11  thf('119', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.11  thf('120', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['118', '119'])).
% 0.92/1.11  thf(t71_relat_1, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.92/1.11       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.92/1.11  thf('121', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 0.92/1.11      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.92/1.11  thf('122', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.11  thf('123', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X2)) = (X2))),
% 0.92/1.11      inference('demod', [status(thm)], ['121', '122'])).
% 0.92/1.11  thf(t80_relat_1, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( v1_relat_1 @ A ) =>
% 0.92/1.11       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.92/1.11  thf('124', plain,
% 0.92/1.11      (![X3 : $i]:
% 0.92/1.11         (((k5_relat_1 @ X3 @ (k6_relat_1 @ (k2_relat_1 @ X3))) = (X3))
% 0.92/1.11          | ~ (v1_relat_1 @ X3))),
% 0.92/1.11      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.92/1.11  thf('125', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.11  thf('126', plain,
% 0.92/1.11      (![X3 : $i]:
% 0.92/1.11         (((k5_relat_1 @ X3 @ (k6_partfun1 @ (k2_relat_1 @ X3))) = (X3))
% 0.92/1.11          | ~ (v1_relat_1 @ X3))),
% 0.92/1.11      inference('demod', [status(thm)], ['124', '125'])).
% 0.92/1.11  thf('127', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.92/1.11            = (k6_partfun1 @ X0))
% 0.92/1.11          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['123', '126'])).
% 0.92/1.11  thf(fc3_funct_1, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.92/1.11       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.92/1.11  thf('128', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.92/1.11      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.92/1.11  thf('129', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.11  thf('130', plain, (![X4 : $i]: (v1_relat_1 @ (k6_partfun1 @ X4))),
% 0.92/1.11      inference('demod', [status(thm)], ['128', '129'])).
% 0.92/1.11  thf('131', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.92/1.11           = (k6_partfun1 @ X0))),
% 0.92/1.11      inference('demod', [status(thm)], ['127', '130'])).
% 0.92/1.11  thf(t63_funct_1, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.92/1.11       ( ![B:$i]:
% 0.92/1.11         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.92/1.11           ( ( ( v2_funct_1 @ A ) & 
% 0.92/1.11               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.92/1.11               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.92/1.11             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.92/1.11  thf('132', plain,
% 0.92/1.11      (![X6 : $i, X7 : $i]:
% 0.92/1.11         (~ (v1_relat_1 @ X6)
% 0.92/1.11          | ~ (v1_funct_1 @ X6)
% 0.92/1.11          | ((X6) = (k2_funct_1 @ X7))
% 0.92/1.11          | ((k5_relat_1 @ X7 @ X6) != (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.92/1.11          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X6))
% 0.92/1.11          | ~ (v2_funct_1 @ X7)
% 0.92/1.11          | ~ (v1_funct_1 @ X7)
% 0.92/1.11          | ~ (v1_relat_1 @ X7))),
% 0.92/1.11      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.92/1.11  thf('133', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.11  thf('134', plain,
% 0.92/1.11      (![X6 : $i, X7 : $i]:
% 0.92/1.11         (~ (v1_relat_1 @ X6)
% 0.92/1.11          | ~ (v1_funct_1 @ X6)
% 0.92/1.11          | ((X6) = (k2_funct_1 @ X7))
% 0.92/1.11          | ((k5_relat_1 @ X7 @ X6) != (k6_partfun1 @ (k1_relat_1 @ X7)))
% 0.92/1.11          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X6))
% 0.92/1.11          | ~ (v2_funct_1 @ X7)
% 0.92/1.11          | ~ (v1_funct_1 @ X7)
% 0.92/1.11          | ~ (v1_relat_1 @ X7))),
% 0.92/1.11      inference('demod', [status(thm)], ['132', '133'])).
% 0.92/1.11  thf('135', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k6_partfun1 @ X0)
% 0.92/1.11            != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 0.92/1.11          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.92/1.11          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.92/1.11          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 0.92/1.11          | ((k2_relat_1 @ (k6_partfun1 @ X0))
% 0.92/1.11              != (k1_relat_1 @ (k6_partfun1 @ X0)))
% 0.92/1.11          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.92/1.11          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.92/1.11          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['131', '134'])).
% 0.92/1.11  thf('136', plain, (![X1 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.92/1.11      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.92/1.11  thf('137', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.11  thf('138', plain, (![X1 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X1)) = (X1))),
% 0.92/1.11      inference('demod', [status(thm)], ['136', '137'])).
% 0.92/1.11  thf('139', plain, (![X4 : $i]: (v1_relat_1 @ (k6_partfun1 @ X4))),
% 0.92/1.11      inference('demod', [status(thm)], ['128', '129'])).
% 0.92/1.11  thf('140', plain, (![X5 : $i]: (v1_funct_1 @ (k6_relat_1 @ X5))),
% 0.92/1.11      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.92/1.11  thf('141', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.11  thf('142', plain, (![X5 : $i]: (v1_funct_1 @ (k6_partfun1 @ X5))),
% 0.92/1.11      inference('demod', [status(thm)], ['140', '141'])).
% 0.92/1.11  thf('143', plain, (![X2 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X2)) = (X2))),
% 0.92/1.11      inference('demod', [status(thm)], ['121', '122'])).
% 0.92/1.11  thf('144', plain, (![X1 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X1)) = (X1))),
% 0.92/1.11      inference('demod', [status(thm)], ['136', '137'])).
% 0.92/1.11  thf('145', plain, (![X5 : $i]: (v1_funct_1 @ (k6_partfun1 @ X5))),
% 0.92/1.11      inference('demod', [status(thm)], ['140', '141'])).
% 0.92/1.11  thf('146', plain, (![X4 : $i]: (v1_relat_1 @ (k6_partfun1 @ X4))),
% 0.92/1.11      inference('demod', [status(thm)], ['128', '129'])).
% 0.92/1.11  thf('147', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 0.92/1.11          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 0.92/1.11          | ((X0) != (X0))
% 0.92/1.11          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0))))),
% 0.92/1.11      inference('demod', [status(thm)],
% 0.92/1.11                ['135', '138', '139', '142', '143', '144', '145', '146'])).
% 0.92/1.11  thf('148', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.92/1.11          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.92/1.11      inference('simplify', [status(thm)], ['147'])).
% 0.92/1.11  thf('149', plain,
% 0.92/1.11      ((~ (v2_funct_1 @ k1_xboole_0)
% 0.92/1.11        | ((k6_partfun1 @ k1_xboole_0)
% 0.92/1.11            = (k2_funct_1 @ (k6_partfun1 @ k1_xboole_0))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['120', '148'])).
% 0.92/1.11  thf('150', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['118', '119'])).
% 0.92/1.11  thf('151', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['118', '119'])).
% 0.92/1.11  thf('152', plain,
% 0.92/1.11      ((~ (v2_funct_1 @ k1_xboole_0)
% 0.92/1.11        | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.92/1.11  thf('153', plain, ((v2_funct_1 @ sk_B)),
% 0.92/1.11      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.92/1.11  thf('154', plain, (((sk_B) = (k1_xboole_0))),
% 0.92/1.11      inference('simplify', [status(thm)], ['116'])).
% 0.92/1.11  thf('155', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.92/1.11      inference('demod', [status(thm)], ['153', '154'])).
% 0.92/1.11  thf('156', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['152', '155'])).
% 0.92/1.11  thf('157', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['118', '119'])).
% 0.92/1.11  thf('158', plain,
% 0.92/1.11      (![X33 : $i]:
% 0.92/1.11         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 0.92/1.11          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.92/1.11      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.92/1.11  thf('159', plain,
% 0.92/1.11      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.92/1.11        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.92/1.11      inference('sup+', [status(thm)], ['157', '158'])).
% 0.92/1.11  thf('160', plain,
% 0.92/1.11      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.11         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.92/1.11          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.92/1.11      inference('simplify', [status(thm)], ['47'])).
% 0.92/1.11  thf('161', plain,
% 0.92/1.11      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.92/1.11      inference('sup-', [status(thm)], ['159', '160'])).
% 0.92/1.11  thf('162', plain, ($false),
% 0.92/1.11      inference('demod', [status(thm)], ['87', '109', '117', '156', '161'])).
% 0.92/1.11  
% 0.92/1.11  % SZS output end Refutation
% 0.92/1.11  
% 0.92/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
