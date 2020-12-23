%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MWcKHOu11P

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:18 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  176 (1028 expanded)
%              Number of leaves         :   35 ( 328 expanded)
%              Depth                    :   17
%              Number of atoms          : 1702 (25911 expanded)
%              Number of equality atoms :   55 ( 165 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_funct_2 @ X29 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v3_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('34',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('38',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X3 ) @ X3 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('44',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('52',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('54',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('55',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('58',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['41','54','55','61','62','65'])).

thf('67',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('68',plain,
    ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['41','54','55','61','62','65'])).

thf('69',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B_1 ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('71',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X31 @ X32 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('76',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['72','73','74','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('80',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('82',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['69','78','79','80','81'])).

thf('83',plain,
    ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','82'])).

thf('84',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','34','83'])).

thf('85',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('86',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('91',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('92',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('94',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X11 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['90','96'])).

thf('98',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('103',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('110',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('111',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('115',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('116',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('117',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('120',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('121',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('123',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X31 @ X32 )
        = X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('126',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X18 @ X19 ) @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v3_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_2 @ X19 @ X18 @ X18 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('133',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['124','125','133'])).

thf('135',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['121','134'])).

thf('136',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114','115','116','117','118','135'])).

thf('137',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['100','137','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MWcKHOu11P
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:18:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 575 iterations in 0.322s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.59/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.78  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.78  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.59/0.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.78  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.59/0.78  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.78  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.59/0.78  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.59/0.78  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.78  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.78  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.59/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.78  thf(t88_funct_2, conjecture,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78       ( ( r2_relset_1 @
% 0.59/0.78           A @ A @ 
% 0.59/0.78           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.59/0.78           ( k6_partfun1 @ A ) ) & 
% 0.59/0.78         ( r2_relset_1 @
% 0.59/0.78           A @ A @ 
% 0.59/0.78           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.59/0.78           ( k6_partfun1 @ A ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i,B:$i]:
% 0.59/0.78        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.78            ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.78            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78          ( ( r2_relset_1 @
% 0.59/0.78              A @ A @ 
% 0.59/0.78              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.59/0.78              ( k6_partfun1 @ A ) ) & 
% 0.59/0.78            ( r2_relset_1 @
% 0.59/0.78              A @ A @ 
% 0.59/0.78              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.59/0.78              ( k6_partfun1 @ A ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.59/0.78  thf('0', plain,
% 0.59/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.59/0.78           (k6_partfun1 @ sk_A))
% 0.59/0.78        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.78              (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.59/0.78             (k6_partfun1 @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('1', plain,
% 0.59/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.78            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.59/0.78           (k6_partfun1 @ sk_A)))
% 0.59/0.78         <= (~
% 0.59/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.78                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.59/0.78               (k6_partfun1 @ sk_A))))),
% 0.59/0.78      inference('split', [status(esa)], ['0'])).
% 0.59/0.78  thf(redefinition_k6_partfun1, axiom,
% 0.59/0.78    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.59/0.78  thf('2', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.78            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.59/0.78           (k6_relat_1 @ sk_A)))
% 0.59/0.78         <= (~
% 0.59/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.78                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.59/0.78               (k6_partfun1 @ sk_A))))),
% 0.59/0.78      inference('demod', [status(thm)], ['1', '2'])).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(redefinition_k2_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (![X28 : $i, X29 : $i]:
% 0.59/0.78         (((k2_funct_2 @ X29 @ X28) = (k2_funct_1 @ X28))
% 0.59/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.59/0.78          | ~ (v3_funct_2 @ X28 @ X29 @ X29)
% 0.59/0.78          | ~ (v1_funct_2 @ X28 @ X29 @ X29)
% 0.59/0.78          | ~ (v1_funct_1 @ X28))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.59/0.78  thf('6', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.78  thf('7', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('8', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('9', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.78  thf('11', plain,
% 0.59/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.59/0.78            sk_B_1) @ 
% 0.59/0.78           (k6_relat_1 @ sk_A)))
% 0.59/0.78         <= (~
% 0.59/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.78                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.59/0.78               (k6_partfun1 @ sk_A))))),
% 0.59/0.78      inference('demod', [status(thm)], ['3', '10'])).
% 0.59/0.78  thf('12', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(dt_k2_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.59/0.78         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.59/0.78         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.59/0.78         ( m1_subset_1 @
% 0.59/0.78           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X18 : $i, X19 : $i]:
% 0.59/0.78         ((m1_subset_1 @ (k2_funct_2 @ X18 @ X19) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.59/0.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.59/0.78          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.59/0.78          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.59/0.78          | ~ (v1_funct_1 @ X19))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.78  thf('14', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.78  thf('15', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('16', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('17', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('18', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.78  thf('19', plain,
% 0.59/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(redefinition_k1_partfun1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.78         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.78         ( v1_funct_1 @ F ) & 
% 0.59/0.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.59/0.78       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.59/0.78          | ~ (v1_funct_1 @ X22)
% 0.59/0.78          | ~ (v1_funct_1 @ X25)
% 0.59/0.78          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.59/0.78          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.59/0.78              = (k5_relat_1 @ X22 @ X25)))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.59/0.78            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.78  thf('23', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.59/0.78            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.78          | ~ (v1_funct_1 @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['22', '23'])).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78            (k2_funct_1 @ sk_B_1))
% 0.59/0.78            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['19', '24'])).
% 0.59/0.78  thf('26', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('27', plain,
% 0.59/0.78      (![X18 : $i, X19 : $i]:
% 0.59/0.78         ((v1_funct_1 @ (k2_funct_2 @ X18 @ X19))
% 0.59/0.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.59/0.78          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.59/0.78          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.59/0.78          | ~ (v1_funct_1 @ X19))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.78  thf('28', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.78  thf('29', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('30', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('31', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('32', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.59/0.78  thf('33', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.78  thf('34', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.78  thf('35', plain,
% 0.59/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.59/0.78  thf(cc1_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( v1_relat_1 @ C ) ))).
% 0.59/0.78  thf('36', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.59/0.78         ((v1_relat_1 @ X5)
% 0.59/0.78          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.78  thf('37', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.78  thf(t65_funct_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.78       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.59/0.78  thf('38', plain,
% 0.59/0.78      (![X4 : $i]:
% 0.59/0.78         (~ (v2_funct_1 @ X4)
% 0.59/0.78          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.59/0.78          | ~ (v1_funct_1 @ X4)
% 0.59/0.78          | ~ (v1_relat_1 @ X4))),
% 0.59/0.78      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.59/0.78  thf(t61_funct_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.78       ( ( v2_funct_1 @ A ) =>
% 0.59/0.78         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.59/0.78             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.59/0.78           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.59/0.78             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      (![X3 : $i]:
% 0.59/0.78         (~ (v2_funct_1 @ X3)
% 0.59/0.78          | ((k5_relat_1 @ (k2_funct_1 @ X3) @ X3)
% 0.59/0.78              = (k6_relat_1 @ (k2_relat_1 @ X3)))
% 0.59/0.78          | ~ (v1_funct_1 @ X3)
% 0.59/0.78          | ~ (v1_relat_1 @ X3))),
% 0.59/0.78      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.78  thf('40', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.59/0.78            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v2_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.78          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.78      inference('sup+', [status(thm)], ['38', '39'])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78        | ~ (v2_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_relat_1 @ sk_B_1)
% 0.59/0.78        | ((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['37', '40'])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.59/0.78  thf(cc2_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.59/0.78         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.59/0.78  thf('43', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X15)
% 0.59/0.78          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.59/0.78          | (v2_funct_1 @ X15)
% 0.59/0.78          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.59/0.78  thf('44', plain,
% 0.59/0.78      (((v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['42', '43'])).
% 0.59/0.78  thf('45', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('46', plain,
% 0.59/0.78      (![X18 : $i, X19 : $i]:
% 0.59/0.78         ((v3_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.59/0.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.59/0.78          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.59/0.78          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.59/0.78          | ~ (v1_funct_1 @ X19))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.78  thf('47', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_1) @ sk_A @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.78  thf('48', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('49', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('50', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('51', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.78  thf('52', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.59/0.78      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.59/0.78  thf('53', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.78  thf('54', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.59/0.78  thf('55', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.78  thf('56', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('57', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X15)
% 0.59/0.78          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.59/0.78          | (v2_funct_1 @ X15)
% 0.59/0.78          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.59/0.78  thf('58', plain,
% 0.59/0.78      (((v2_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v1_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['56', '57'])).
% 0.59/0.78  thf('59', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('60', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('61', plain, ((v2_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.59/0.78  thf('62', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('63', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('64', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.59/0.78         ((v1_relat_1 @ X5)
% 0.59/0.78          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.78  thf('65', plain, ((v1_relat_1 @ sk_B_1)),
% 0.59/0.78      inference('sup-', [status(thm)], ['63', '64'])).
% 0.59/0.78  thf('66', plain,
% 0.59/0.78      (((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.59/0.78      inference('demod', [status(thm)], ['41', '54', '55', '61', '62', '65'])).
% 0.59/0.78  thf('67', plain,
% 0.59/0.78      (![X3 : $i]:
% 0.59/0.78         (~ (v2_funct_1 @ X3)
% 0.59/0.78          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 0.59/0.78              = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.59/0.78          | ~ (v1_funct_1 @ X3)
% 0.59/0.78          | ~ (v1_relat_1 @ X3))),
% 0.59/0.78      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.78  thf('68', plain,
% 0.59/0.78      (((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.59/0.78      inference('demod', [status(thm)], ['41', '54', '55', '61', '62', '65'])).
% 0.59/0.78  thf('69', plain,
% 0.59/0.78      ((((k6_relat_1 @ (k1_relat_1 @ sk_B_1))
% 0.59/0.78          = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))
% 0.59/0.78        | ~ (v1_relat_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('sup+', [status(thm)], ['67', '68'])).
% 0.59/0.78  thf('70', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(t67_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.59/0.78  thf('71', plain,
% 0.59/0.78      (![X31 : $i, X32 : $i]:
% 0.59/0.78         (((k1_relset_1 @ X31 @ X31 @ X32) = (X31))
% 0.59/0.78          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.59/0.78          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.59/0.78          | ~ (v1_funct_1 @ X32))),
% 0.59/0.78      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.59/0.78  thf('72', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.78  thf('73', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('74', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('75', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(redefinition_k1_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.59/0.78  thf('76', plain,
% 0.59/0.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.78         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.59/0.78          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.78  thf('77', plain,
% 0.59/0.78      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['75', '76'])).
% 0.59/0.78  thf('78', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['72', '73', '74', '77'])).
% 0.59/0.78  thf('79', plain, ((v1_relat_1 @ sk_B_1)),
% 0.59/0.78      inference('sup-', [status(thm)], ['63', '64'])).
% 0.59/0.78  thf('80', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('81', plain, ((v2_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.59/0.78  thf('82', plain,
% 0.59/0.78      (((k6_relat_1 @ sk_A)
% 0.59/0.78         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '78', '79', '80', '81'])).
% 0.59/0.78  thf('83', plain,
% 0.59/0.78      (((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) = (k6_relat_1 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['66', '82'])).
% 0.59/0.78  thf('84', plain,
% 0.59/0.78      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78         (k2_funct_1 @ sk_B_1)) = (k6_relat_1 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['25', '34', '83'])).
% 0.59/0.78  thf('85', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.78  thf('86', plain,
% 0.59/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.59/0.78           (k6_partfun1 @ sk_A)))
% 0.59/0.78         <= (~
% 0.59/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.59/0.78               (k6_partfun1 @ sk_A))))),
% 0.59/0.78      inference('split', [status(esa)], ['0'])).
% 0.59/0.78  thf('87', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.78  thf('88', plain,
% 0.59/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.59/0.78           (k6_relat_1 @ sk_A)))
% 0.59/0.78         <= (~
% 0.59/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.59/0.78               (k6_partfun1 @ sk_A))))),
% 0.59/0.78      inference('demod', [status(thm)], ['86', '87'])).
% 0.59/0.78  thf('89', plain,
% 0.59/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78            (k2_funct_1 @ sk_B_1)) @ 
% 0.59/0.78           (k6_relat_1 @ sk_A)))
% 0.59/0.78         <= (~
% 0.59/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.59/0.78               (k6_partfun1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['85', '88'])).
% 0.59/0.78  thf('90', plain,
% 0.59/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.59/0.78           (k6_relat_1 @ sk_A)))
% 0.59/0.78         <= (~
% 0.59/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.59/0.78               (k6_partfun1 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['84', '89'])).
% 0.59/0.78  thf(dt_k6_partfun1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( m1_subset_1 @
% 0.59/0.78         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.59/0.78       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.59/0.78  thf('91', plain,
% 0.59/0.78      (![X21 : $i]:
% 0.59/0.78         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 0.59/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.59/0.78  thf('92', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.78  thf('93', plain,
% 0.59/0.78      (![X21 : $i]:
% 0.59/0.78         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 0.59/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.59/0.78      inference('demod', [status(thm)], ['91', '92'])).
% 0.59/0.78  thf(reflexivity_r2_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.78     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.78       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.59/0.78  thf('94', plain,
% 0.59/0.78      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.78         ((r2_relset_1 @ X11 @ X12 @ X13 @ X13)
% 0.59/0.78          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.59/0.78          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.59/0.78      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.59/0.78  thf('95', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.59/0.78      inference('condensation', [status(thm)], ['94'])).
% 0.59/0.78  thf('96', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['93', '95'])).
% 0.59/0.78  thf('97', plain,
% 0.59/0.78      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.59/0.78         (k6_partfun1 @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['90', '96'])).
% 0.59/0.78  thf('98', plain,
% 0.59/0.78      (~
% 0.59/0.78       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.78          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.59/0.78         (k6_partfun1 @ sk_A))) | 
% 0.59/0.78       ~
% 0.59/0.78       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.59/0.78          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.59/0.78         (k6_partfun1 @ sk_A)))),
% 0.59/0.78      inference('split', [status(esa)], ['0'])).
% 0.59/0.78  thf('99', plain,
% 0.59/0.78      (~
% 0.59/0.78       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.59/0.78          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.59/0.78         (k6_partfun1 @ sk_A)))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['97', '98'])).
% 0.59/0.78  thf('100', plain,
% 0.59/0.78      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.59/0.78           sk_B_1) @ 
% 0.59/0.78          (k6_relat_1 @ sk_A))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['11', '99'])).
% 0.59/0.78  thf('101', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('102', plain,
% 0.59/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.59/0.78  thf('103', plain,
% 0.59/0.78      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.59/0.78          | ~ (v1_funct_1 @ X22)
% 0.59/0.78          | ~ (v1_funct_1 @ X25)
% 0.59/0.78          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.59/0.78          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.59/0.78              = (k5_relat_1 @ X22 @ X25)))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.59/0.78  thf('104', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.59/0.78            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['102', '103'])).
% 0.59/0.78  thf('105', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.78  thf('106', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.59/0.78            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.78          | ~ (v1_funct_1 @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['104', '105'])).
% 0.59/0.78  thf('107', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_B_1)
% 0.59/0.78        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.59/0.78            sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['101', '106'])).
% 0.59/0.78  thf('108', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('109', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.78  thf('110', plain,
% 0.59/0.78      (![X4 : $i]:
% 0.59/0.78         (~ (v2_funct_1 @ X4)
% 0.59/0.78          | ((k2_funct_1 @ (k2_funct_1 @ X4)) = (X4))
% 0.59/0.78          | ~ (v1_funct_1 @ X4)
% 0.59/0.78          | ~ (v1_relat_1 @ X4))),
% 0.59/0.78      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.59/0.78  thf('111', plain,
% 0.59/0.78      (![X3 : $i]:
% 0.59/0.78         (~ (v2_funct_1 @ X3)
% 0.59/0.78          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 0.59/0.78              = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.59/0.78          | ~ (v1_funct_1 @ X3)
% 0.59/0.78          | ~ (v1_relat_1 @ X3))),
% 0.59/0.78      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.78  thf('112', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.59/0.78            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v2_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.78          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.59/0.78      inference('sup+', [status(thm)], ['110', '111'])).
% 0.59/0.78  thf('113', plain,
% 0.59/0.78      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78        | ~ (v2_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_relat_1 @ sk_B_1)
% 0.59/0.78        | ((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)
% 0.59/0.78            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B_1)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['109', '112'])).
% 0.59/0.78  thf('114', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.59/0.78  thf('115', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.78  thf('116', plain, ((v2_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.59/0.78  thf('117', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('118', plain, ((v1_relat_1 @ sk_B_1)),
% 0.59/0.78      inference('sup-', [status(thm)], ['63', '64'])).
% 0.59/0.78  thf('119', plain,
% 0.59/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.59/0.78  thf('120', plain,
% 0.59/0.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.78         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.59/0.78          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.78  thf('121', plain,
% 0.59/0.78      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78         = (k1_relat_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['119', '120'])).
% 0.59/0.78  thf('122', plain,
% 0.59/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.59/0.78  thf('123', plain,
% 0.59/0.78      (![X31 : $i, X32 : $i]:
% 0.59/0.78         (((k1_relset_1 @ X31 @ X31 @ X32) = (X31))
% 0.59/0.78          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.59/0.78          | ~ (v1_funct_2 @ X32 @ X31 @ X31)
% 0.59/0.78          | ~ (v1_funct_1 @ X32))),
% 0.59/0.78      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.59/0.78  thf('124', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.59/0.78        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.59/0.78        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1)) = (sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['122', '123'])).
% 0.59/0.78  thf('125', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.78  thf('126', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('127', plain,
% 0.59/0.78      (![X18 : $i, X19 : $i]:
% 0.59/0.78         ((v1_funct_2 @ (k2_funct_2 @ X18 @ X19) @ X18 @ X18)
% 0.59/0.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.59/0.78          | ~ (v3_funct_2 @ X19 @ X18 @ X18)
% 0.59/0.78          | ~ (v1_funct_2 @ X19 @ X18 @ X18)
% 0.59/0.78          | ~ (v1_funct_1 @ X19))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.78  thf('128', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.59/0.78        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_1) @ sk_A @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['126', '127'])).
% 0.59/0.78  thf('129', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('130', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('131', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('132', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.59/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.59/0.78  thf('133', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.59/0.78      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 0.59/0.78  thf('134', plain,
% 0.59/0.78      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1)) = (sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['124', '125', '133'])).
% 0.59/0.78  thf('135', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B_1)) = (sk_A))),
% 0.59/0.78      inference('sup+', [status(thm)], ['121', '134'])).
% 0.59/0.78  thf('136', plain,
% 0.59/0.78      (((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) = (k6_relat_1 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)],
% 0.59/0.78                ['113', '114', '115', '116', '117', '118', '135'])).
% 0.59/0.78  thf('137', plain,
% 0.59/0.78      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.59/0.78         sk_B_1) = (k6_relat_1 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['107', '108', '136'])).
% 0.59/0.78  thf('138', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['93', '95'])).
% 0.59/0.78  thf('139', plain, ($false),
% 0.59/0.78      inference('demod', [status(thm)], ['100', '137', '138'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
