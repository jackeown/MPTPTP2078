%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r9GdHpmNxg

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:11 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  180 (1040 expanded)
%              Number of leaves         :   37 ( 332 expanded)
%              Depth                    :   15
%              Number of atoms          : 1724 (25967 expanded)
%              Number of equality atoms :   55 ( 165 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( ( k2_funct_2 @ X32 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('31',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
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
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X21 @ X22 ) @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
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
    inference(demod,[status(thm)],['29','30'])).

thf('54',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('55',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v3_funct_2 @ X18 @ X19 @ X20 )
      | ( v2_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('64',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('72',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X34 @ X35 )
        = X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X21 @ X22 ) @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v3_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('82',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B_1 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['73','74','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['70','83'])).

thf('85',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','54','55','61','62','67','84'])).

thf('86',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','85'])).

thf('87',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('90',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_1 ) @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('93',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('94',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('96',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['92','98'])).

thf('100',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_1 ) @ sk_B_1 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('104',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('111',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('112',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('113',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X5 ) @ X5 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['44','52','53'])).

thf('117',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('118',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('119',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['65','66'])).

thf('121',plain,
    ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119','120'])).

thf('122',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('123',plain,
    ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119','120'])).

thf('124',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_B_1 ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X34 @ X35 )
        = X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('127',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('132',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['127','128','129','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['65','66'])).

thf('135',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('137',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['124','133','134','135','136'])).

thf('138',plain,
    ( ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['121','137'])).

thf('139',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['102','139','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r9GdHpmNxg
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 380 iterations in 0.204s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.47/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.47/0.65  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.47/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.65  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.65  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.47/0.65  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.65  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.65  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.47/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.65  thf(t88_funct_2, conjecture,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( v3_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.65       ( ( r2_relset_1 @
% 0.47/0.65           A @ A @ 
% 0.47/0.65           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.47/0.65           ( k6_partfun1 @ A ) ) & 
% 0.47/0.65         ( r2_relset_1 @
% 0.47/0.65           A @ A @ 
% 0.47/0.65           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.47/0.65           ( k6_partfun1 @ A ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i,B:$i]:
% 0.47/0.65        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.47/0.65            ( v3_funct_2 @ B @ A @ A ) & 
% 0.47/0.65            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.65          ( ( r2_relset_1 @
% 0.47/0.65              A @ A @ 
% 0.47/0.65              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.47/0.65              ( k6_partfun1 @ A ) ) & 
% 0.47/0.65            ( r2_relset_1 @
% 0.47/0.65              A @ A @ 
% 0.47/0.65              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.47/0.65              ( k6_partfun1 @ A ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.47/0.65           (k6_partfun1 @ sk_A))
% 0.47/0.65        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.47/0.65              (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.47/0.65             (k6_partfun1 @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.47/0.65           (k6_partfun1 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.47/0.65               (k6_partfun1 @ sk_A))))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf(redefinition_k6_partfun1, axiom,
% 0.47/0.65    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.65  thf('2', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65            (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.47/0.65           (k6_relat_1 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.47/0.65               (k6_partfun1 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['1', '2'])).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(redefinition_k2_funct_2, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( v3_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.65       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X31 : $i, X32 : $i]:
% 0.47/0.65         (((k2_funct_2 @ X32 @ X31) = (k2_funct_1 @ X31))
% 0.47/0.65          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.47/0.65          | ~ (v3_funct_2 @ X31 @ X32 @ X32)
% 0.47/0.65          | ~ (v1_funct_2 @ X31 @ X32 @ X32)
% 0.47/0.65          | ~ (v1_funct_1 @ X31))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.65  thf('7', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('8', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('9', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65            (k2_funct_1 @ sk_B_1)) @ 
% 0.47/0.65           (k6_relat_1 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65                (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.47/0.65               (k6_partfun1 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['3', '10'])).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(dt_k2_funct_2, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( v3_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.65       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.47/0.65         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.47/0.65         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.47/0.65         ( m1_subset_1 @
% 0.47/0.65           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      (![X21 : $i, X22 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (k2_funct_2 @ X21 @ X22) @ 
% 0.47/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.47/0.65          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.47/0.65          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.47/0.65          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.47/0.65          | ~ (v1_funct_1 @ X22))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_1) @ 
% 0.47/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.65  thf('16', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('17', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('18', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('19', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.47/0.65  thf(redefinition_k1_partfun1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.47/0.65     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.65         ( v1_funct_1 @ F ) & 
% 0.47/0.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.47/0.65       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.47/0.65          | ~ (v1_funct_1 @ X25)
% 0.47/0.65          | ~ (v1_funct_1 @ X28)
% 0.47/0.65          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.47/0.65          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 0.47/0.65              = (k5_relat_1 @ X25 @ X28)))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.47/0.65            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X21 : $i, X22 : $i]:
% 0.47/0.65         ((v1_funct_1 @ (k2_funct_2 @ X21 @ X22))
% 0.47/0.65          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.47/0.65          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.47/0.65          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.47/0.65          | ~ (v1_funct_1 @ X22))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.65  thf('26', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('27', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('28', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('29', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.47/0.65  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.47/0.65  thf('31', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_1) @ X0)
% 0.47/0.65            = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ X0))
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.47/0.65          | ~ (v1_funct_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['22', '31'])).
% 0.47/0.65  thf('33', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_B_1)
% 0.47/0.65        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.47/0.65            sk_B_1) = (k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['12', '32'])).
% 0.47/0.65  thf('34', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.47/0.65  thf(cc1_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( v1_relat_1 @ C ) ))).
% 0.47/0.65  thf('36', plain,
% 0.47/0.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.65         ((v1_relat_1 @ X8)
% 0.47/0.65          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.65  thf('37', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.65  thf(t65_funct_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.65       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.47/0.65  thf('38', plain,
% 0.47/0.65      (![X7 : $i]:
% 0.47/0.65         (~ (v2_funct_1 @ X7)
% 0.47/0.65          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.47/0.65          | ~ (v1_funct_1 @ X7)
% 0.47/0.65          | ~ (v1_relat_1 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.47/0.65  thf(t61_funct_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.65       ( ( v2_funct_1 @ A ) =>
% 0.47/0.65         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.47/0.65             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.47/0.65           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.47/0.65             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.65  thf('39', plain,
% 0.47/0.65      (![X5 : $i]:
% 0.47/0.65         (~ (v2_funct_1 @ X5)
% 0.47/0.65          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.47/0.65              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.47/0.65          | ~ (v1_funct_1 @ X5)
% 0.47/0.65          | ~ (v1_relat_1 @ X5))),
% 0.47/0.65      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.47/0.65  thf('40', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.47/0.65            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ~ (v2_funct_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['38', '39'])).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65        | ~ (v2_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_relat_1 @ sk_B_1)
% 0.47/0.65        | ((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1)
% 0.47/0.65            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B_1)))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['37', '40'])).
% 0.47/0.65  thf('42', plain,
% 0.47/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.47/0.65  thf(cc2_funct_2, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.47/0.65         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.47/0.65  thf('43', plain,
% 0.47/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.65         (~ (v1_funct_1 @ X18)
% 0.47/0.65          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 0.47/0.65          | (v2_funct_1 @ X18)
% 0.47/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      (((v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.65  thf('45', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('46', plain,
% 0.47/0.65      (![X21 : $i, X22 : $i]:
% 0.47/0.65         ((v3_funct_2 @ (k2_funct_2 @ X21 @ X22) @ X21 @ X21)
% 0.47/0.65          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.47/0.65          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.47/0.65          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.47/0.65          | ~ (v1_funct_1 @ X22))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.47/0.65  thf('47', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_1) @ sk_A @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['45', '46'])).
% 0.47/0.65  thf('48', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('49', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('50', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('51', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.47/0.65  thf('52', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.47/0.65      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.47/0.65  thf('53', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf('54', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.47/0.65  thf('55', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('57', plain,
% 0.47/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.65         (~ (v1_funct_1 @ X18)
% 0.47/0.65          | ~ (v3_funct_2 @ X18 @ X19 @ X20)
% 0.47/0.65          | (v2_funct_1 @ X18)
% 0.47/0.65          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.47/0.65  thf('58', plain,
% 0.47/0.65      (((v2_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v1_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.65  thf('59', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('60', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('61', plain, ((v2_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.47/0.65  thf('62', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('63', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(cc2_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.65  thf('64', plain,
% 0.47/0.65      (![X1 : $i, X2 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.47/0.65          | (v1_relat_1 @ X1)
% 0.47/0.65          | ~ (v1_relat_1 @ X2))),
% 0.47/0.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.65  thf('65', plain,
% 0.47/0.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.65  thf(fc6_relat_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.65  thf('66', plain,
% 0.47/0.65      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.65  thf('67', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.65      inference('demod', [status(thm)], ['65', '66'])).
% 0.47/0.65  thf('68', plain,
% 0.47/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.47/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.65  thf('69', plain,
% 0.47/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.47/0.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.65  thf('70', plain,
% 0.47/0.65      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65         = (k1_relat_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['68', '69'])).
% 0.47/0.65  thf('71', plain,
% 0.47/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.47/0.65  thf(t67_funct_2, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.47/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.47/0.65       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.47/0.65  thf('72', plain,
% 0.47/0.65      (![X34 : $i, X35 : $i]:
% 0.47/0.65         (((k1_relset_1 @ X34 @ X34 @ X35) = (X34))
% 0.47/0.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.47/0.65          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 0.47/0.65          | ~ (v1_funct_1 @ X35))),
% 0.47/0.65      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.47/0.65  thf('73', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)
% 0.47/0.65        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1)) = (sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.47/0.65  thf('74', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf('75', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('76', plain,
% 0.47/0.65      (![X21 : $i, X22 : $i]:
% 0.47/0.65         ((v1_funct_2 @ (k2_funct_2 @ X21 @ X22) @ X21 @ X21)
% 0.47/0.65          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.47/0.65          | ~ (v3_funct_2 @ X22 @ X21 @ X21)
% 0.47/0.65          | ~ (v1_funct_2 @ X22 @ X21 @ X21)
% 0.47/0.65          | ~ (v1_funct_1 @ X22))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.47/0.65  thf('77', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_1) @ sk_A @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['75', '76'])).
% 0.47/0.65  thf('78', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('79', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('80', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('81', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.47/0.65  thf('82', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B_1) @ sk_A @ sk_A)),
% 0.47/0.65      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.47/0.65  thf('83', plain,
% 0.47/0.65      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1)) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['73', '74', '82'])).
% 0.47/0.65  thf('84', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_B_1)) = (sk_A))),
% 0.47/0.65      inference('sup+', [status(thm)], ['70', '83'])).
% 0.47/0.65  thf('85', plain,
% 0.47/0.65      (((k5_relat_1 @ (k2_funct_1 @ sk_B_1) @ sk_B_1) = (k6_relat_1 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['41', '54', '55', '61', '62', '67', '84'])).
% 0.47/0.65  thf('86', plain,
% 0.47/0.65      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.47/0.65         sk_B_1) = (k6_relat_1 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['33', '34', '85'])).
% 0.47/0.65  thf('87', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.47/0.65  thf('88', plain,
% 0.47/0.65      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.47/0.65            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.47/0.65           (k6_partfun1 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.47/0.65                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.47/0.65               (k6_partfun1 @ sk_A))))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('89', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.65  thf('90', plain,
% 0.47/0.65      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.47/0.65            (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.47/0.65           (k6_relat_1 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.47/0.65                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.47/0.65               (k6_partfun1 @ sk_A))))),
% 0.47/0.65      inference('demod', [status(thm)], ['88', '89'])).
% 0.47/0.65  thf('91', plain,
% 0.47/0.65      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_1) @ 
% 0.47/0.65            sk_B_1) @ 
% 0.47/0.65           (k6_relat_1 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.47/0.65                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.47/0.65               (k6_partfun1 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['87', '90'])).
% 0.47/0.65  thf('92', plain,
% 0.47/0.65      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.47/0.65           (k6_relat_1 @ sk_A)))
% 0.47/0.65         <= (~
% 0.47/0.65             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.47/0.65                (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.47/0.65               (k6_partfun1 @ sk_A))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['86', '91'])).
% 0.47/0.65  thf(dt_k6_partfun1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( m1_subset_1 @
% 0.47/0.65         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.47/0.65       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.47/0.65  thf('93', plain,
% 0.47/0.65      (![X24 : $i]:
% 0.47/0.65         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.47/0.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.47/0.65  thf('94', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.65  thf('95', plain,
% 0.47/0.65      (![X24 : $i]:
% 0.47/0.65         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 0.47/0.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.47/0.65      inference('demod', [status(thm)], ['93', '94'])).
% 0.47/0.65  thf(reflexivity_r2_relset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.65     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.65       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.47/0.65  thf('96', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.65         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.47/0.65          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.47/0.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.47/0.65      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.47/0.65  thf('97', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.47/0.65      inference('condensation', [status(thm)], ['96'])).
% 0.47/0.65  thf('98', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['95', '97'])).
% 0.47/0.65  thf('99', plain,
% 0.47/0.65      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.47/0.65          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.47/0.65         (k6_partfun1 @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['92', '98'])).
% 0.47/0.65  thf('100', plain,
% 0.47/0.65      (~
% 0.47/0.65       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.47/0.65         (k6_partfun1 @ sk_A))) | 
% 0.47/0.65       ~
% 0.47/0.65       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.47/0.65          (k2_funct_2 @ sk_A @ sk_B_1) @ sk_B_1) @ 
% 0.47/0.65         (k6_partfun1 @ sk_A)))),
% 0.47/0.65      inference('split', [status(esa)], ['0'])).
% 0.47/0.65  thf('101', plain,
% 0.47/0.65      (~
% 0.47/0.65       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65          (k2_funct_2 @ sk_A @ sk_B_1)) @ 
% 0.47/0.65         (k6_partfun1 @ sk_A)))),
% 0.47/0.65      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 0.47/0.65  thf('102', plain,
% 0.47/0.65      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.65          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65           (k2_funct_1 @ sk_B_1)) @ 
% 0.47/0.65          (k6_relat_1 @ sk_A))),
% 0.47/0.65      inference('simpl_trail', [status(thm)], ['11', '101'])).
% 0.47/0.65  thf('103', plain,
% 0.47/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.47/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.47/0.65  thf('104', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('105', plain,
% 0.47/0.65      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.47/0.65          | ~ (v1_funct_1 @ X25)
% 0.47/0.65          | ~ (v1_funct_1 @ X28)
% 0.47/0.65          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.47/0.65          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 0.47/0.65              = (k5_relat_1 @ X25 @ X28)))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.47/0.65  thf('106', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.47/0.65            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['104', '105'])).
% 0.47/0.65  thf('107', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('108', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.65         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 0.47/0.65            = (k5_relat_1 @ sk_B_1 @ X0))
% 0.47/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.47/0.65          | ~ (v1_funct_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['106', '107'])).
% 0.47/0.65  thf('109', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65            (k2_funct_1 @ sk_B_1))
% 0.47/0.65            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['103', '108'])).
% 0.47/0.65  thf('110', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf('111', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.65  thf('112', plain,
% 0.47/0.65      (![X7 : $i]:
% 0.47/0.65         (~ (v2_funct_1 @ X7)
% 0.47/0.65          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.47/0.65          | ~ (v1_funct_1 @ X7)
% 0.47/0.65          | ~ (v1_relat_1 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.47/0.65  thf('113', plain,
% 0.47/0.65      (![X5 : $i]:
% 0.47/0.65         (~ (v2_funct_1 @ X5)
% 0.47/0.65          | ((k5_relat_1 @ (k2_funct_1 @ X5) @ X5)
% 0.47/0.65              = (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.47/0.65          | ~ (v1_funct_1 @ X5)
% 0.47/0.65          | ~ (v1_relat_1 @ X5))),
% 0.47/0.65      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.47/0.65  thf('114', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.47/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_funct_1 @ X0)
% 0.47/0.65          | ~ (v2_funct_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['112', '113'])).
% 0.47/0.65  thf('115', plain,
% 0.47/0.65      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65        | ~ (v2_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_relat_1 @ sk_B_1)
% 0.47/0.65        | ((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['111', '114'])).
% 0.47/0.65  thf('116', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['44', '52', '53'])).
% 0.47/0.65  thf('117', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.65  thf('118', plain, ((v2_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.47/0.65  thf('119', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('120', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.65      inference('demod', [status(thm)], ['65', '66'])).
% 0.47/0.65  thf('121', plain,
% 0.47/0.65      (((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['115', '116', '117', '118', '119', '120'])).
% 0.47/0.65  thf('122', plain,
% 0.47/0.65      (![X5 : $i]:
% 0.47/0.65         (~ (v2_funct_1 @ X5)
% 0.47/0.65          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.47/0.65              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.47/0.65          | ~ (v1_funct_1 @ X5)
% 0.47/0.65          | ~ (v1_relat_1 @ X5))),
% 0.47/0.65      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.47/0.65  thf('123', plain,
% 0.47/0.65      (((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 0.47/0.65         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.47/0.65      inference('demod', [status(thm)],
% 0.47/0.65                ['115', '116', '117', '118', '119', '120'])).
% 0.47/0.65  thf('124', plain,
% 0.47/0.65      ((((k6_relat_1 @ (k1_relat_1 @ sk_B_1))
% 0.47/0.65          = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))
% 0.47/0.65        | ~ (v1_relat_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v2_funct_1 @ sk_B_1))),
% 0.47/0.65      inference('sup+', [status(thm)], ['122', '123'])).
% 0.47/0.65  thf('125', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('126', plain,
% 0.47/0.65      (![X34 : $i, X35 : $i]:
% 0.47/0.65         (((k1_relset_1 @ X34 @ X34 @ X35) = (X34))
% 0.47/0.65          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.47/0.65          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 0.47/0.65          | ~ (v1_funct_1 @ X35))),
% 0.47/0.65      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.47/0.65  thf('127', plain,
% 0.47/0.65      ((~ (v1_funct_1 @ sk_B_1)
% 0.47/0.65        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.47/0.65        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['125', '126'])).
% 0.47/0.65  thf('128', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('129', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('130', plain,
% 0.47/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('131', plain,
% 0.47/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.65         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.47/0.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.65  thf('132', plain,
% 0.47/0.65      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['130', '131'])).
% 0.47/0.65  thf('133', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['127', '128', '129', '132'])).
% 0.47/0.65  thf('134', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.65      inference('demod', [status(thm)], ['65', '66'])).
% 0.47/0.65  thf('135', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('136', plain, ((v2_funct_1 @ sk_B_1)),
% 0.47/0.65      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.47/0.65  thf('137', plain,
% 0.47/0.65      (((k6_relat_1 @ sk_A)
% 0.47/0.65         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_B_1))))),
% 0.47/0.65      inference('demod', [status(thm)], ['124', '133', '134', '135', '136'])).
% 0.47/0.65  thf('138', plain,
% 0.47/0.65      (((k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)) = (k6_relat_1 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['121', '137'])).
% 0.47/0.65  thf('139', plain,
% 0.47/0.65      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ 
% 0.47/0.65         (k2_funct_1 @ sk_B_1)) = (k6_relat_1 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['109', '110', '138'])).
% 0.47/0.65  thf('140', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['95', '97'])).
% 0.47/0.65  thf('141', plain, ($false),
% 0.47/0.65      inference('demod', [status(thm)], ['102', '139', '140'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
