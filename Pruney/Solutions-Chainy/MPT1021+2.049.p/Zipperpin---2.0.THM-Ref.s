%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5UCwS4PyB1

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:18 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  176 (1028 expanded)
%              Number of leaves         :   35 ( 328 expanded)
%              Depth                    :   17
%              Number of atoms          : 1702 (25911 expanded)
%              Number of equality atoms :   55 ( 165 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_funct_2 @ X30 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('34',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('38',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
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
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('44',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X17 @ X18 ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('52',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('54',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('55',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('58',plain,
    ( ( v2_funct_1 @ sk_B )
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
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','54','55','61','62','65'])).

thf('67',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('68',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','54','55','61','62','65'])).

thf('69',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('71',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X32 @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('76',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['72','73','74','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('82',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','78','79','80','81'])).

thf('83',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','82'])).

thf('84',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','34','83'])).

thf('85',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('86',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('91',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('92',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('94',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_relset_1 @ X10 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['90','96'])).

thf('98',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('103',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('110',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('111',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
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
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('115',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('116',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('117',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('120',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('121',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('123',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X32 @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('124',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('126',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X17 @ X18 ) @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v3_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_2 @ X18 @ X17 @ X17 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('133',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['124','125','133'])).

thf('135',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['121','134'])).

thf('136',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114','115','116','117','118','135'])).

thf('137',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5UCwS4PyB1
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.78  % Solved by: fo/fo7.sh
% 0.58/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.78  % done 563 iterations in 0.325s
% 0.58/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.78  % SZS output start Refutation
% 0.58/0.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.58/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.78  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.58/0.78  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.58/0.78  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.58/0.78  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.58/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.78  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.58/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.78  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.58/0.78  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.58/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.78  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.58/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.78  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.58/0.78  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.78  thf(t88_funct_2, conjecture,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.58/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.58/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.58/0.78       ( ( r2_relset_1 @
% 0.58/0.78           A @ A @ 
% 0.58/0.78           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.58/0.78           ( k6_partfun1 @ A ) ) & 
% 0.58/0.78         ( r2_relset_1 @
% 0.58/0.78           A @ A @ 
% 0.58/0.78           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.58/0.78           ( k6_partfun1 @ A ) ) ) ))).
% 0.58/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.78    (~( ![A:$i,B:$i]:
% 0.58/0.78        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.58/0.78            ( v3_funct_2 @ B @ A @ A ) & 
% 0.58/0.78            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.58/0.78          ( ( r2_relset_1 @
% 0.58/0.78              A @ A @ 
% 0.58/0.78              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.58/0.78              ( k6_partfun1 @ A ) ) & 
% 0.58/0.78            ( r2_relset_1 @
% 0.58/0.78              A @ A @ 
% 0.58/0.78              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.58/0.78              ( k6_partfun1 @ A ) ) ) ) )),
% 0.58/0.78    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.58/0.78  thf('0', plain,
% 0.58/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.58/0.78           (k6_partfun1 @ sk_A))
% 0.58/0.78        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.58/0.78              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.58/0.78             (k6_partfun1 @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('1', plain,
% 0.58/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.58/0.78            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.58/0.78           (k6_partfun1 @ sk_A)))
% 0.58/0.78         <= (~
% 0.58/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.58/0.78                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.58/0.78               (k6_partfun1 @ sk_A))))),
% 0.58/0.78      inference('split', [status(esa)], ['0'])).
% 0.58/0.78  thf(redefinition_k6_partfun1, axiom,
% 0.58/0.78    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.58/0.78  thf('2', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.58/0.78  thf('3', plain,
% 0.58/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.58/0.78            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.58/0.78           (k6_relat_1 @ sk_A)))
% 0.58/0.78         <= (~
% 0.58/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.58/0.78                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.58/0.78               (k6_partfun1 @ sk_A))))),
% 0.58/0.78      inference('demod', [status(thm)], ['1', '2'])).
% 0.58/0.78  thf('4', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(redefinition_k2_funct_2, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.58/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.58/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.58/0.78       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.58/0.78  thf('5', plain,
% 0.58/0.78      (![X29 : $i, X30 : $i]:
% 0.58/0.78         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 0.58/0.78          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.58/0.78          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 0.58/0.78          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 0.58/0.78          | ~ (v1_funct_1 @ X29))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.58/0.78  thf('6', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.78  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.58/0.78  thf('11', plain,
% 0.58/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.58/0.78            sk_B) @ 
% 0.58/0.78           (k6_relat_1 @ sk_A)))
% 0.58/0.78         <= (~
% 0.58/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.58/0.78                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.58/0.78               (k6_partfun1 @ sk_A))))),
% 0.58/0.78      inference('demod', [status(thm)], ['3', '10'])).
% 0.58/0.78  thf('12', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(dt_k2_funct_2, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.58/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.58/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.58/0.78       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.58/0.78         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.58/0.78         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.58/0.78         ( m1_subset_1 @
% 0.58/0.78           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.58/0.78  thf('13', plain,
% 0.58/0.78      (![X17 : $i, X18 : $i]:
% 0.58/0.78         ((m1_subset_1 @ (k2_funct_2 @ X17 @ X18) @ 
% 0.58/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.58/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.58/0.78          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.58/0.78          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.58/0.78          | ~ (v1_funct_1 @ X18))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.58/0.78  thf('14', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.58/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.78  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('16', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('17', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('18', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.58/0.78  thf('19', plain,
% 0.58/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.58/0.78  thf('20', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(redefinition_k1_partfun1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.58/0.78     ( ( ( v1_funct_1 @ E ) & 
% 0.58/0.78         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.78         ( v1_funct_1 @ F ) & 
% 0.58/0.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.58/0.78       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.58/0.78  thf('21', plain,
% 0.58/0.78      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.58/0.78          | ~ (v1_funct_1 @ X23)
% 0.58/0.78          | ~ (v1_funct_1 @ X26)
% 0.58/0.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.58/0.78          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.58/0.78              = (k5_relat_1 @ X23 @ X26)))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.58/0.78  thf('22', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.58/0.78            = (k5_relat_1 @ sk_B @ X0))
% 0.58/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.78  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('24', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.58/0.78            = (k5_relat_1 @ sk_B @ X0))
% 0.58/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.58/0.78          | ~ (v1_funct_1 @ X0))),
% 0.58/0.78      inference('demod', [status(thm)], ['22', '23'])).
% 0.58/0.78  thf('25', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.58/0.78        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['19', '24'])).
% 0.58/0.78  thf('26', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('27', plain,
% 0.58/0.78      (![X17 : $i, X18 : $i]:
% 0.58/0.78         ((v1_funct_1 @ (k2_funct_2 @ X17 @ X18))
% 0.58/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.58/0.78          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.58/0.78          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.58/0.78          | ~ (v1_funct_1 @ X18))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.58/0.78  thf('28', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.78  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('30', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('31', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('32', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.58/0.78  thf('33', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.58/0.78  thf('34', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.58/0.78  thf('35', plain,
% 0.58/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.58/0.78  thf(cc1_relset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.78       ( v1_relat_1 @ C ) ))).
% 0.58/0.78  thf('36', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.78         ((v1_relat_1 @ X4)
% 0.58/0.78          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.78  thf('37', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.78  thf(t65_funct_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.78       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.58/0.78  thf('38', plain,
% 0.58/0.78      (![X3 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X3)
% 0.58/0.78          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.58/0.78          | ~ (v1_funct_1 @ X3)
% 0.58/0.78          | ~ (v1_relat_1 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.58/0.78  thf(t61_funct_1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.78       ( ( v2_funct_1 @ A ) =>
% 0.58/0.78         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.58/0.78             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.58/0.78           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.58/0.78             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.78  thf('39', plain,
% 0.58/0.78      (![X1 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X1)
% 0.58/0.78          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.58/0.78              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.58/0.78          | ~ (v1_funct_1 @ X1)
% 0.58/0.78          | ~ (v1_relat_1 @ X1))),
% 0.58/0.78      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.58/0.78  thf('40', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.58/0.78            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.58/0.78          | ~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v2_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.58/0.78      inference('sup+', [status(thm)], ['38', '39'])).
% 0.58/0.78  thf('41', plain,
% 0.58/0.78      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.58/0.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.58/0.78        | ~ (v2_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v1_relat_1 @ sk_B)
% 0.58/0.78        | ((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.58/0.78            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['37', '40'])).
% 0.58/0.78  thf('42', plain,
% 0.58/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.58/0.78  thf(cc2_funct_2, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.78       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.58/0.78         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.58/0.78  thf('43', plain,
% 0.58/0.78      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.78         (~ (v1_funct_1 @ X14)
% 0.58/0.78          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.58/0.78          | (v2_funct_1 @ X14)
% 0.58/0.78          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.58/0.78  thf('44', plain,
% 0.58/0.78      (((v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.58/0.78        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.58/0.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.78  thf('45', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('46', plain,
% 0.58/0.78      (![X17 : $i, X18 : $i]:
% 0.58/0.78         ((v3_funct_2 @ (k2_funct_2 @ X17 @ X18) @ X17 @ X17)
% 0.58/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.58/0.78          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.58/0.78          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.58/0.78          | ~ (v1_funct_1 @ X18))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.58/0.78  thf('47', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['45', '46'])).
% 0.58/0.78  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('49', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('50', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('51', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.58/0.78  thf('52', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.58/0.78      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.58/0.78  thf('53', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.58/0.78  thf('54', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.58/0.78  thf('55', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.58/0.78  thf('56', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('57', plain,
% 0.58/0.78      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.78         (~ (v1_funct_1 @ X14)
% 0.58/0.78          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.58/0.78          | (v2_funct_1 @ X14)
% 0.58/0.78          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.58/0.78  thf('58', plain,
% 0.58/0.78      (((v2_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['56', '57'])).
% 0.58/0.78  thf('59', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('61', plain, ((v2_funct_1 @ sk_B)),
% 0.58/0.78      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.58/0.78  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('63', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('64', plain,
% 0.58/0.78      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.78         ((v1_relat_1 @ X4)
% 0.58/0.78          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.58/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.78  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.78      inference('sup-', [status(thm)], ['63', '64'])).
% 0.58/0.78  thf('66', plain,
% 0.58/0.78      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.58/0.78         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['41', '54', '55', '61', '62', '65'])).
% 0.58/0.78  thf('67', plain,
% 0.58/0.78      (![X1 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X1)
% 0.58/0.78          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.58/0.78              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.58/0.78          | ~ (v1_funct_1 @ X1)
% 0.58/0.78          | ~ (v1_relat_1 @ X1))),
% 0.58/0.78      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.58/0.78  thf('68', plain,
% 0.58/0.78      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))
% 0.58/0.78         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['41', '54', '55', '61', '62', '65'])).
% 0.58/0.78  thf('69', plain,
% 0.58/0.78      ((((k6_relat_1 @ (k1_relat_1 @ sk_B))
% 0.58/0.78          = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))
% 0.58/0.78        | ~ (v1_relat_1 @ sk_B)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v2_funct_1 @ sk_B))),
% 0.58/0.78      inference('sup+', [status(thm)], ['67', '68'])).
% 0.58/0.78  thf('70', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(t67_funct_2, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.58/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.58/0.78       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.58/0.78  thf('71', plain,
% 0.58/0.78      (![X32 : $i, X33 : $i]:
% 0.58/0.78         (((k1_relset_1 @ X32 @ X32 @ X33) = (X32))
% 0.58/0.78          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.58/0.78          | ~ (v1_funct_2 @ X33 @ X32 @ X32)
% 0.58/0.78          | ~ (v1_funct_1 @ X33))),
% 0.58/0.78      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.58/0.78  thf('72', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['70', '71'])).
% 0.58/0.78  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('74', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('75', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i]:
% 0.58/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.78  thf('76', plain,
% 0.58/0.78      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.58/0.78         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.58/0.78          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.78  thf('77', plain,
% 0.58/0.78      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['75', '76'])).
% 0.58/0.78  thf('78', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['72', '73', '74', '77'])).
% 0.58/0.78  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.78      inference('sup-', [status(thm)], ['63', '64'])).
% 0.58/0.78  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('81', plain, ((v2_funct_1 @ sk_B)),
% 0.58/0.78      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.58/0.78  thf('82', plain,
% 0.58/0.78      (((k6_relat_1 @ sk_A) = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.58/0.78      inference('demod', [status(thm)], ['69', '78', '79', '80', '81'])).
% 0.58/0.78  thf('83', plain,
% 0.58/0.78      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['66', '82'])).
% 0.58/0.78  thf('84', plain,
% 0.58/0.78      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.58/0.78         = (k6_relat_1 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['25', '34', '83'])).
% 0.58/0.78  thf('85', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.58/0.78  thf('86', plain,
% 0.58/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.58/0.78           (k6_partfun1 @ sk_A)))
% 0.58/0.78         <= (~
% 0.58/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.58/0.78               (k6_partfun1 @ sk_A))))),
% 0.58/0.78      inference('split', [status(esa)], ['0'])).
% 0.58/0.78  thf('87', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.58/0.78  thf('88', plain,
% 0.58/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.58/0.78           (k6_relat_1 @ sk_A)))
% 0.58/0.78         <= (~
% 0.58/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.58/0.78               (k6_partfun1 @ sk_A))))),
% 0.58/0.78      inference('demod', [status(thm)], ['86', '87'])).
% 0.58/0.78  thf('89', plain,
% 0.58/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78            (k2_funct_1 @ sk_B)) @ 
% 0.58/0.78           (k6_relat_1 @ sk_A)))
% 0.58/0.78         <= (~
% 0.58/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.58/0.78               (k6_partfun1 @ sk_A))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['85', '88'])).
% 0.58/0.78  thf('90', plain,
% 0.58/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.58/0.78           (k6_relat_1 @ sk_A)))
% 0.58/0.78         <= (~
% 0.58/0.78             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.58/0.78               (k6_partfun1 @ sk_A))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['84', '89'])).
% 0.58/0.78  thf(dt_k6_partfun1, axiom,
% 0.58/0.78    (![A:$i]:
% 0.58/0.78     ( ( m1_subset_1 @
% 0.58/0.78         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.58/0.78       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.58/0.78  thf('91', plain,
% 0.58/0.78      (![X20 : $i]:
% 0.58/0.78         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 0.58/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.58/0.78  thf('92', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.58/0.78  thf('93', plain,
% 0.58/0.78      (![X20 : $i]:
% 0.58/0.78         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 0.58/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 0.58/0.78      inference('demod', [status(thm)], ['91', '92'])).
% 0.58/0.78  thf(reflexivity_r2_relset_1, axiom,
% 0.58/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.78     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.78       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.58/0.78  thf('94', plain,
% 0.58/0.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.78         ((r2_relset_1 @ X10 @ X11 @ X12 @ X12)
% 0.58/0.78          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.58/0.78          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.58/0.78      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.58/0.78  thf('95', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.58/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.58/0.78      inference('condensation', [status(thm)], ['94'])).
% 0.58/0.78  thf('96', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['93', '95'])).
% 0.58/0.78  thf('97', plain,
% 0.58/0.78      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.58/0.78         (k6_partfun1 @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['90', '96'])).
% 0.58/0.78  thf('98', plain,
% 0.58/0.78      (~
% 0.58/0.78       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.58/0.78          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.58/0.78         (k6_partfun1 @ sk_A))) | 
% 0.58/0.78       ~
% 0.58/0.78       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.58/0.78          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.58/0.78         (k6_partfun1 @ sk_A)))),
% 0.58/0.78      inference('split', [status(esa)], ['0'])).
% 0.58/0.78  thf('99', plain,
% 0.58/0.78      (~
% 0.58/0.78       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.58/0.78          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.58/0.78         (k6_partfun1 @ sk_A)))),
% 0.58/0.78      inference('sat_resolution*', [status(thm)], ['97', '98'])).
% 0.58/0.78  thf('100', plain,
% 0.58/0.78      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.58/0.78          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.58/0.78          (k6_relat_1 @ sk_A))),
% 0.58/0.78      inference('simpl_trail', [status(thm)], ['11', '99'])).
% 0.58/0.78  thf('101', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('102', plain,
% 0.58/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.58/0.78  thf('103', plain,
% 0.58/0.78      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.78         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.58/0.78          | ~ (v1_funct_1 @ X23)
% 0.58/0.78          | ~ (v1_funct_1 @ X26)
% 0.58/0.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.58/0.78          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.58/0.78              = (k5_relat_1 @ X23 @ X26)))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.58/0.78  thf('104', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.58/0.78            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.58/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['102', '103'])).
% 0.58/0.78  thf('105', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.58/0.78  thf('106', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.58/0.78            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.58/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.58/0.78          | ~ (v1_funct_1 @ X0))),
% 0.58/0.78      inference('demod', [status(thm)], ['104', '105'])).
% 0.58/0.78  thf('107', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ sk_B)
% 0.58/0.78        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.58/0.78            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['101', '106'])).
% 0.58/0.78  thf('108', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('109', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.78  thf('110', plain,
% 0.58/0.78      (![X3 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X3)
% 0.58/0.78          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.58/0.78          | ~ (v1_funct_1 @ X3)
% 0.58/0.78          | ~ (v1_relat_1 @ X3))),
% 0.58/0.78      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.58/0.78  thf('111', plain,
% 0.58/0.78      (![X1 : $i]:
% 0.58/0.78         (~ (v2_funct_1 @ X1)
% 0.58/0.78          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.58/0.78              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.58/0.78          | ~ (v1_funct_1 @ X1)
% 0.58/0.78          | ~ (v1_relat_1 @ X1))),
% 0.58/0.78      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.58/0.78  thf('112', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.58/0.78            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.58/0.78          | ~ (v1_relat_1 @ X0)
% 0.58/0.78          | ~ (v1_funct_1 @ X0)
% 0.58/0.78          | ~ (v2_funct_1 @ X0)
% 0.58/0.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.78          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.58/0.78      inference('sup+', [status(thm)], ['110', '111'])).
% 0.58/0.78  thf('113', plain,
% 0.58/0.78      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.58/0.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.58/0.78        | ~ (v2_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v1_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v1_relat_1 @ sk_B)
% 0.58/0.78        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.58/0.78            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.58/0.78      inference('sup-', [status(thm)], ['109', '112'])).
% 0.58/0.78  thf('114', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.58/0.78  thf('115', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.58/0.78  thf('116', plain, ((v2_funct_1 @ sk_B)),
% 0.58/0.78      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.58/0.78  thf('117', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('118', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.78      inference('sup-', [status(thm)], ['63', '64'])).
% 0.58/0.78  thf('119', plain,
% 0.58/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.58/0.78  thf('120', plain,
% 0.58/0.78      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.58/0.78         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.58/0.78          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.58/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.78  thf('121', plain,
% 0.58/0.78      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B))
% 0.58/0.78         = (k1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['119', '120'])).
% 0.58/0.78  thf('122', plain,
% 0.58/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.58/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.58/0.78  thf('123', plain,
% 0.58/0.78      (![X32 : $i, X33 : $i]:
% 0.58/0.78         (((k1_relset_1 @ X32 @ X32 @ X33) = (X32))
% 0.58/0.78          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.58/0.78          | ~ (v1_funct_2 @ X33 @ X32 @ X32)
% 0.58/0.78          | ~ (v1_funct_1 @ X33))),
% 0.58/0.78      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.58/0.78  thf('124', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.58/0.78        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.58/0.78        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['122', '123'])).
% 0.58/0.78  thf('125', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['32', '33'])).
% 0.58/0.78  thf('126', plain,
% 0.58/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('127', plain,
% 0.58/0.78      (![X17 : $i, X18 : $i]:
% 0.58/0.78         ((v1_funct_2 @ (k2_funct_2 @ X17 @ X18) @ X17 @ X17)
% 0.58/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))
% 0.58/0.78          | ~ (v3_funct_2 @ X18 @ X17 @ X17)
% 0.58/0.78          | ~ (v1_funct_2 @ X18 @ X17 @ X17)
% 0.58/0.78          | ~ (v1_funct_1 @ X18))),
% 0.58/0.78      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.58/0.78  thf('128', plain,
% 0.58/0.78      ((~ (v1_funct_1 @ sk_B)
% 0.58/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.58/0.78        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['126', '127'])).
% 0.58/0.78  thf('129', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('130', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('131', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.58/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.78  thf('132', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.58/0.78      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.58/0.78  thf('133', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.58/0.78      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 0.58/0.78  thf('134', plain,
% 0.58/0.78      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['124', '125', '133'])).
% 0.58/0.78  thf('135', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.58/0.78      inference('sup+', [status(thm)], ['121', '134'])).
% 0.58/0.78  thf('136', plain,
% 0.58/0.78      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)],
% 0.58/0.78                ['113', '114', '115', '116', '117', '118', '135'])).
% 0.58/0.78  thf('137', plain,
% 0.58/0.78      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.58/0.78         = (k6_relat_1 @ sk_A))),
% 0.58/0.78      inference('demod', [status(thm)], ['107', '108', '136'])).
% 0.58/0.78  thf('138', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['93', '95'])).
% 0.58/0.78  thf('139', plain, ($false),
% 0.58/0.78      inference('demod', [status(thm)], ['100', '137', '138'])).
% 0.58/0.78  
% 0.58/0.78  % SZS output end Refutation
% 0.58/0.78  
% 0.58/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
