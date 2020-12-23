%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nQjX3LZgBl

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:13 EST 2020

% Result     : Theorem 54.47s
% Output     : Refutation 54.47s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 696 expanded)
%              Number of leaves         :   46 ( 230 expanded)
%              Depth                    :   16
%              Number of atoms          : 1869 (13972 expanded)
%              Number of equality atoms :   72 ( 193 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( ( k2_funct_2 @ X39 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('20',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('31',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_2 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('37',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['37','38','39'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_funct_2 @ X27 @ X26 )
      | ( ( k2_relat_1 @ X27 )
        = X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['42','45','48'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('51',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('52',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('59',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('65',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','62','63','64'])).

thf('66',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('67',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X11 = X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('71',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('72',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('73',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 )
      | ( X11 != X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('74',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','75'])).

thf('77',plain,
    ( ( r2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('80',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('81',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('83',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82'])).

thf('84',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['69','83'])).

thf('85',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','84'])).

thf('86',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('93',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','95'])).

thf('97',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('98',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('107',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('108',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('110',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('111',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('113',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('114',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('116',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('117',plain,(
    ! [X18: $i] :
      ( zip_tseitin_0 @ X18 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['115','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['118'])).

thf('120',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['114','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('122',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('123',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120','123'])).

thf('125',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('126',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['124','127'])).

thf('129',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120','123'])).

thf('130',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('131',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('133',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('135',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120','123'])).

thf('137',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['136','139'])).

thf('141',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120','123'])).

thf('142',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120','123'])).

thf('143',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('144',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('146',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144','145'])).

thf('147',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','146'])).

thf('148',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','108','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['96','148','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nQjX3LZgBl
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:56:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 54.47/54.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 54.47/54.76  % Solved by: fo/fo7.sh
% 54.47/54.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.47/54.76  % done 12261 iterations in 54.284s
% 54.47/54.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 54.47/54.76  % SZS output start Refutation
% 54.47/54.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 54.47/54.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 54.47/54.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 54.47/54.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 54.47/54.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 54.47/54.76  thf(sk_B_type, type, sk_B: $i).
% 54.47/54.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 54.47/54.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 54.47/54.76  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 54.47/54.76  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 54.47/54.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 54.47/54.76  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 54.47/54.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 54.47/54.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 54.47/54.76  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 54.47/54.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 54.47/54.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 54.47/54.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 54.47/54.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 54.47/54.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 54.47/54.76  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 54.47/54.76  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 54.47/54.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 54.47/54.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 54.47/54.76  thf(sk_A_type, type, sk_A: $i).
% 54.47/54.76  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 54.47/54.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 54.47/54.76  thf(t88_funct_2, conjecture,
% 54.47/54.76    (![A:$i,B:$i]:
% 54.47/54.76     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 54.47/54.76         ( v3_funct_2 @ B @ A @ A ) & 
% 54.47/54.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 54.47/54.76       ( ( r2_relset_1 @
% 54.47/54.76           A @ A @ 
% 54.47/54.76           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 54.47/54.76           ( k6_partfun1 @ A ) ) & 
% 54.47/54.76         ( r2_relset_1 @
% 54.47/54.76           A @ A @ 
% 54.47/54.76           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 54.47/54.76           ( k6_partfun1 @ A ) ) ) ))).
% 54.47/54.76  thf(zf_stmt_0, negated_conjecture,
% 54.47/54.76    (~( ![A:$i,B:$i]:
% 54.47/54.76        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 54.47/54.76            ( v3_funct_2 @ B @ A @ A ) & 
% 54.47/54.76            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 54.47/54.76          ( ( r2_relset_1 @
% 54.47/54.76              A @ A @ 
% 54.47/54.76              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 54.47/54.76              ( k6_partfun1 @ A ) ) & 
% 54.47/54.76            ( r2_relset_1 @
% 54.47/54.76              A @ A @ 
% 54.47/54.76              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 54.47/54.76              ( k6_partfun1 @ A ) ) ) ) )),
% 54.47/54.76    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 54.47/54.76  thf('0', plain,
% 54.47/54.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 54.47/54.76            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 54.47/54.76           (k6_partfun1 @ sk_A))
% 54.47/54.76        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 54.47/54.76              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 54.47/54.76             (k6_partfun1 @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('1', plain,
% 54.47/54.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 54.47/54.76            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 54.47/54.76           (k6_partfun1 @ sk_A)))
% 54.47/54.76         <= (~
% 54.47/54.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 54.47/54.76                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 54.47/54.76               (k6_partfun1 @ sk_A))))),
% 54.47/54.76      inference('split', [status(esa)], ['0'])).
% 54.47/54.76  thf(redefinition_k6_partfun1, axiom,
% 54.47/54.76    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 54.47/54.76  thf('2', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 54.47/54.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 54.47/54.76  thf('3', plain,
% 54.47/54.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 54.47/54.76            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 54.47/54.76           (k6_relat_1 @ sk_A)))
% 54.47/54.76         <= (~
% 54.47/54.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 54.47/54.76                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 54.47/54.76               (k6_partfun1 @ sk_A))))),
% 54.47/54.76      inference('demod', [status(thm)], ['1', '2'])).
% 54.47/54.76  thf('4', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf(redefinition_k2_funct_2, axiom,
% 54.47/54.76    (![A:$i,B:$i]:
% 54.47/54.76     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 54.47/54.76         ( v3_funct_2 @ B @ A @ A ) & 
% 54.47/54.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 54.47/54.76       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 54.47/54.76  thf('5', plain,
% 54.47/54.76      (![X38 : $i, X39 : $i]:
% 54.47/54.76         (((k2_funct_2 @ X39 @ X38) = (k2_funct_1 @ X38))
% 54.47/54.76          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 54.47/54.76          | ~ (v3_funct_2 @ X38 @ X39 @ X39)
% 54.47/54.76          | ~ (v1_funct_2 @ X38 @ X39 @ X39)
% 54.47/54.76          | ~ (v1_funct_1 @ X38))),
% 54.47/54.76      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 54.47/54.76  thf('6', plain,
% 54.47/54.76      ((~ (v1_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 54.47/54.76        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 54.47/54.76        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 54.47/54.76      inference('sup-', [status(thm)], ['4', '5'])).
% 54.47/54.76  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 54.47/54.76  thf('11', plain,
% 54.47/54.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 54.47/54.76            (k2_funct_1 @ sk_B)) @ 
% 54.47/54.76           (k6_relat_1 @ sk_A)))
% 54.47/54.76         <= (~
% 54.47/54.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 54.47/54.76                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 54.47/54.76               (k6_partfun1 @ sk_A))))),
% 54.47/54.76      inference('demod', [status(thm)], ['3', '10'])).
% 54.47/54.76  thf('12', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('13', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf(dt_k2_funct_2, axiom,
% 54.47/54.76    (![A:$i,B:$i]:
% 54.47/54.76     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 54.47/54.76         ( v3_funct_2 @ B @ A @ A ) & 
% 54.47/54.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 54.47/54.76       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 54.47/54.76         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 54.47/54.76         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 54.47/54.76         ( m1_subset_1 @
% 54.47/54.76           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 54.47/54.76  thf('14', plain,
% 54.47/54.76      (![X28 : $i, X29 : $i]:
% 54.47/54.76         ((m1_subset_1 @ (k2_funct_2 @ X28 @ X29) @ 
% 54.47/54.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 54.47/54.76          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 54.47/54.76          | ~ (v3_funct_2 @ X29 @ X28 @ X28)
% 54.47/54.76          | ~ (v1_funct_2 @ X29 @ X28 @ X28)
% 54.47/54.76          | ~ (v1_funct_1 @ X29))),
% 54.47/54.76      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 54.47/54.76  thf('15', plain,
% 54.47/54.76      ((~ (v1_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 54.47/54.76        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 54.47/54.76        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 54.47/54.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 54.47/54.76      inference('sup-', [status(thm)], ['13', '14'])).
% 54.47/54.76  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('19', plain,
% 54.47/54.76      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 54.47/54.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 54.47/54.76  thf(redefinition_k1_partfun1, axiom,
% 54.47/54.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 54.47/54.76     ( ( ( v1_funct_1 @ E ) & 
% 54.47/54.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 54.47/54.76         ( v1_funct_1 @ F ) & 
% 54.47/54.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 54.47/54.76       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 54.47/54.76  thf('20', plain,
% 54.47/54.76      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 54.47/54.76         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 54.47/54.76          | ~ (v1_funct_1 @ X32)
% 54.47/54.76          | ~ (v1_funct_1 @ X35)
% 54.47/54.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 54.47/54.76          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 54.47/54.76              = (k5_relat_1 @ X32 @ X35)))),
% 54.47/54.76      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 54.47/54.76  thf('21', plain,
% 54.47/54.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.47/54.76         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 54.47/54.76            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 54.47/54.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 54.47/54.76          | ~ (v1_funct_1 @ X0)
% 54.47/54.76          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 54.47/54.76      inference('sup-', [status(thm)], ['19', '20'])).
% 54.47/54.76  thf('22', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('23', plain,
% 54.47/54.76      (![X28 : $i, X29 : $i]:
% 54.47/54.76         ((v1_funct_1 @ (k2_funct_2 @ X28 @ X29))
% 54.47/54.76          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 54.47/54.76          | ~ (v3_funct_2 @ X29 @ X28 @ X28)
% 54.47/54.76          | ~ (v1_funct_2 @ X29 @ X28 @ X28)
% 54.47/54.76          | ~ (v1_funct_1 @ X29))),
% 54.47/54.76      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 54.47/54.76  thf('24', plain,
% 54.47/54.76      ((~ (v1_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 54.47/54.76        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 54.47/54.76        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 54.47/54.76      inference('sup-', [status(thm)], ['22', '23'])).
% 54.47/54.76  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('26', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('28', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 54.47/54.76  thf('29', plain,
% 54.47/54.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.47/54.76         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 54.47/54.76            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 54.47/54.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 54.47/54.76          | ~ (v1_funct_1 @ X0))),
% 54.47/54.76      inference('demod', [status(thm)], ['21', '28'])).
% 54.47/54.76  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 54.47/54.76  thf('31', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 54.47/54.76  thf('32', plain,
% 54.47/54.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.47/54.76         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 54.47/54.76            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 54.47/54.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 54.47/54.76          | ~ (v1_funct_1 @ X0))),
% 54.47/54.76      inference('demod', [status(thm)], ['29', '30', '31'])).
% 54.47/54.76  thf('33', plain,
% 54.47/54.76      ((~ (v1_funct_1 @ sk_B)
% 54.47/54.76        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 54.47/54.76            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 54.47/54.76      inference('sup-', [status(thm)], ['12', '32'])).
% 54.47/54.76  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('35', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf(cc2_funct_2, axiom,
% 54.47/54.76    (![A:$i,B:$i,C:$i]:
% 54.47/54.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.47/54.76       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 54.47/54.76         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 54.47/54.76  thf('36', plain,
% 54.47/54.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 54.47/54.76         (~ (v1_funct_1 @ X15)
% 54.47/54.76          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 54.47/54.76          | (v2_funct_2 @ X15 @ X17)
% 54.47/54.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 54.47/54.76      inference('cnf', [status(esa)], [cc2_funct_2])).
% 54.47/54.76  thf('37', plain,
% 54.47/54.76      (((v2_funct_2 @ sk_B @ sk_A)
% 54.47/54.76        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 54.47/54.76        | ~ (v1_funct_1 @ sk_B))),
% 54.47/54.76      inference('sup-', [status(thm)], ['35', '36'])).
% 54.47/54.76  thf('38', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('40', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 54.47/54.76      inference('demod', [status(thm)], ['37', '38', '39'])).
% 54.47/54.76  thf(d3_funct_2, axiom,
% 54.47/54.76    (![A:$i,B:$i]:
% 54.47/54.76     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 54.47/54.76       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 54.47/54.76  thf('41', plain,
% 54.47/54.76      (![X26 : $i, X27 : $i]:
% 54.47/54.76         (~ (v2_funct_2 @ X27 @ X26)
% 54.47/54.76          | ((k2_relat_1 @ X27) = (X26))
% 54.47/54.76          | ~ (v5_relat_1 @ X27 @ X26)
% 54.47/54.76          | ~ (v1_relat_1 @ X27))),
% 54.47/54.76      inference('cnf', [status(esa)], [d3_funct_2])).
% 54.47/54.76  thf('42', plain,
% 54.47/54.76      ((~ (v1_relat_1 @ sk_B)
% 54.47/54.76        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 54.47/54.76        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 54.47/54.76      inference('sup-', [status(thm)], ['40', '41'])).
% 54.47/54.76  thf('43', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf(cc1_relset_1, axiom,
% 54.47/54.76    (![A:$i,B:$i,C:$i]:
% 54.47/54.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.47/54.76       ( v1_relat_1 @ C ) ))).
% 54.47/54.76  thf('44', plain,
% 54.47/54.76      (![X2 : $i, X3 : $i, X4 : $i]:
% 54.47/54.76         ((v1_relat_1 @ X2)
% 54.47/54.76          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 54.47/54.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 54.47/54.76  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 54.47/54.76      inference('sup-', [status(thm)], ['43', '44'])).
% 54.47/54.76  thf('46', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf(cc2_relset_1, axiom,
% 54.47/54.76    (![A:$i,B:$i,C:$i]:
% 54.47/54.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.47/54.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 54.47/54.76  thf('47', plain,
% 54.47/54.76      (![X5 : $i, X6 : $i, X7 : $i]:
% 54.47/54.76         ((v5_relat_1 @ X5 @ X7)
% 54.47/54.76          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 54.47/54.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 54.47/54.76  thf('48', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 54.47/54.76      inference('sup-', [status(thm)], ['46', '47'])).
% 54.47/54.76  thf('49', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 54.47/54.76      inference('demod', [status(thm)], ['42', '45', '48'])).
% 54.47/54.76  thf(t61_funct_1, axiom,
% 54.47/54.76    (![A:$i]:
% 54.47/54.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 54.47/54.76       ( ( v2_funct_1 @ A ) =>
% 54.47/54.76         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 54.47/54.76             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 54.47/54.76           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 54.47/54.76             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 54.47/54.76  thf('50', plain,
% 54.47/54.76      (![X1 : $i]:
% 54.47/54.76         (~ (v2_funct_1 @ X1)
% 54.47/54.76          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 54.47/54.76              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 54.47/54.76          | ~ (v1_funct_1 @ X1)
% 54.47/54.76          | ~ (v1_relat_1 @ X1))),
% 54.47/54.76      inference('cnf', [status(esa)], [t61_funct_1])).
% 54.47/54.76  thf(dt_k6_partfun1, axiom,
% 54.47/54.76    (![A:$i]:
% 54.47/54.76     ( ( m1_subset_1 @
% 54.47/54.76         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 54.47/54.76       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 54.47/54.76  thf('51', plain,
% 54.47/54.76      (![X31 : $i]:
% 54.47/54.76         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 54.47/54.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 54.47/54.76      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 54.47/54.76  thf('52', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 54.47/54.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 54.47/54.76  thf('53', plain,
% 54.47/54.76      (![X31 : $i]:
% 54.47/54.76         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 54.47/54.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 54.47/54.76      inference('demod', [status(thm)], ['51', '52'])).
% 54.47/54.76  thf('54', plain,
% 54.47/54.76      (![X0 : $i]:
% 54.47/54.76         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 54.47/54.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 54.47/54.76          | ~ (v1_relat_1 @ X0)
% 54.47/54.76          | ~ (v1_funct_1 @ X0)
% 54.47/54.76          | ~ (v2_funct_1 @ X0))),
% 54.47/54.76      inference('sup+', [status(thm)], ['50', '53'])).
% 54.47/54.76  thf('55', plain,
% 54.47/54.76      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 54.47/54.76         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 54.47/54.76        | ~ (v2_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v1_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v1_relat_1 @ sk_B))),
% 54.47/54.76      inference('sup+', [status(thm)], ['49', '54'])).
% 54.47/54.76  thf('56', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 54.47/54.76      inference('demod', [status(thm)], ['42', '45', '48'])).
% 54.47/54.76  thf('57', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('58', plain,
% 54.47/54.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 54.47/54.76         (~ (v1_funct_1 @ X15)
% 54.47/54.76          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 54.47/54.76          | (v2_funct_1 @ X15)
% 54.47/54.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 54.47/54.76      inference('cnf', [status(esa)], [cc2_funct_2])).
% 54.47/54.76  thf('59', plain,
% 54.47/54.76      (((v2_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 54.47/54.76        | ~ (v1_funct_1 @ sk_B))),
% 54.47/54.76      inference('sup-', [status(thm)], ['57', '58'])).
% 54.47/54.76  thf('60', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('62', plain, ((v2_funct_1 @ sk_B)),
% 54.47/54.76      inference('demod', [status(thm)], ['59', '60', '61'])).
% 54.47/54.76  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 54.47/54.76      inference('sup-', [status(thm)], ['43', '44'])).
% 54.47/54.76  thf('65', plain,
% 54.47/54.76      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 54.47/54.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('demod', [status(thm)], ['55', '56', '62', '63', '64'])).
% 54.47/54.76  thf('66', plain,
% 54.47/54.76      (![X31 : $i]:
% 54.47/54.76         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 54.47/54.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 54.47/54.76      inference('demod', [status(thm)], ['51', '52'])).
% 54.47/54.76  thf(redefinition_r2_relset_1, axiom,
% 54.47/54.76    (![A:$i,B:$i,C:$i,D:$i]:
% 54.47/54.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 54.47/54.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 54.47/54.76       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 54.47/54.76  thf('67', plain,
% 54.47/54.76      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 54.47/54.76         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 54.47/54.76          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 54.47/54.76          | ((X11) = (X14))
% 54.47/54.76          | ~ (r2_relset_1 @ X12 @ X13 @ X11 @ X14))),
% 54.47/54.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 54.47/54.76  thf('68', plain,
% 54.47/54.76      (![X0 : $i, X1 : $i]:
% 54.47/54.76         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 54.47/54.76          | ((k6_relat_1 @ X0) = (X1))
% 54.47/54.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 54.47/54.76      inference('sup-', [status(thm)], ['66', '67'])).
% 54.47/54.76  thf('69', plain,
% 54.47/54.76      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 54.47/54.76        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 54.47/54.76             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 54.47/54.76      inference('sup-', [status(thm)], ['65', '68'])).
% 54.47/54.76  thf('70', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 54.47/54.76      inference('demod', [status(thm)], ['42', '45', '48'])).
% 54.47/54.76  thf('71', plain,
% 54.47/54.76      (![X1 : $i]:
% 54.47/54.76         (~ (v2_funct_1 @ X1)
% 54.47/54.76          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 54.47/54.76              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 54.47/54.76          | ~ (v1_funct_1 @ X1)
% 54.47/54.76          | ~ (v1_relat_1 @ X1))),
% 54.47/54.76      inference('cnf', [status(esa)], [t61_funct_1])).
% 54.47/54.76  thf('72', plain,
% 54.47/54.76      (![X31 : $i]:
% 54.47/54.76         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 54.47/54.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 54.47/54.76      inference('demod', [status(thm)], ['51', '52'])).
% 54.47/54.76  thf('73', plain,
% 54.47/54.76      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 54.47/54.76         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 54.47/54.76          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 54.47/54.76          | (r2_relset_1 @ X12 @ X13 @ X11 @ X14)
% 54.47/54.76          | ((X11) != (X14)))),
% 54.47/54.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 54.47/54.76  thf('74', plain,
% 54.47/54.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 54.47/54.76         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 54.47/54.76          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 54.47/54.76      inference('simplify', [status(thm)], ['73'])).
% 54.47/54.76  thf('75', plain,
% 54.47/54.76      (![X0 : $i]:
% 54.47/54.76         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 54.47/54.76      inference('sup-', [status(thm)], ['72', '74'])).
% 54.47/54.76  thf('76', plain,
% 54.47/54.76      (![X0 : $i]:
% 54.47/54.76         ((r2_relset_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 54.47/54.76           (k6_relat_1 @ (k2_relat_1 @ X0)) @ 
% 54.47/54.76           (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 54.47/54.76          | ~ (v1_relat_1 @ X0)
% 54.47/54.76          | ~ (v1_funct_1 @ X0)
% 54.47/54.76          | ~ (v2_funct_1 @ X0))),
% 54.47/54.76      inference('sup+', [status(thm)], ['71', '75'])).
% 54.47/54.76  thf('77', plain,
% 54.47/54.76      (((r2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ 
% 54.47/54.76         (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 54.47/54.76         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 54.47/54.76        | ~ (v2_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v1_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v1_relat_1 @ sk_B))),
% 54.47/54.76      inference('sup+', [status(thm)], ['70', '76'])).
% 54.47/54.76  thf('78', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 54.47/54.76      inference('demod', [status(thm)], ['42', '45', '48'])).
% 54.47/54.76  thf('79', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 54.47/54.76      inference('demod', [status(thm)], ['42', '45', '48'])).
% 54.47/54.76  thf('80', plain, ((v2_funct_1 @ sk_B)),
% 54.47/54.76      inference('demod', [status(thm)], ['59', '60', '61'])).
% 54.47/54.76  thf('81', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 54.47/54.76      inference('sup-', [status(thm)], ['43', '44'])).
% 54.47/54.76  thf('83', plain,
% 54.47/54.76      ((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 54.47/54.76        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['77', '78', '79', '80', '81', '82'])).
% 54.47/54.76  thf('84', plain,
% 54.47/54.76      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['69', '83'])).
% 54.47/54.76  thf('85', plain,
% 54.47/54.76      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 54.47/54.76         = (k6_relat_1 @ sk_A))),
% 54.47/54.76      inference('demod', [status(thm)], ['33', '34', '84'])).
% 54.47/54.76  thf('86', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 54.47/54.76  thf('87', plain,
% 54.47/54.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 54.47/54.76            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 54.47/54.76           (k6_partfun1 @ sk_A)))
% 54.47/54.76         <= (~
% 54.47/54.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 54.47/54.76                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 54.47/54.76               (k6_partfun1 @ sk_A))))),
% 54.47/54.76      inference('split', [status(esa)], ['0'])).
% 54.47/54.76  thf('88', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 54.47/54.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 54.47/54.76  thf('89', plain,
% 54.47/54.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 54.47/54.76            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 54.47/54.76           (k6_relat_1 @ sk_A)))
% 54.47/54.76         <= (~
% 54.47/54.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 54.47/54.76                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 54.47/54.76               (k6_partfun1 @ sk_A))))),
% 54.47/54.76      inference('demod', [status(thm)], ['87', '88'])).
% 54.47/54.76  thf('90', plain,
% 54.47/54.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 54.47/54.76            sk_B) @ 
% 54.47/54.76           (k6_relat_1 @ sk_A)))
% 54.47/54.76         <= (~
% 54.47/54.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 54.47/54.76                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 54.47/54.76               (k6_partfun1 @ sk_A))))),
% 54.47/54.76      inference('sup-', [status(thm)], ['86', '89'])).
% 54.47/54.76  thf('91', plain,
% 54.47/54.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 54.47/54.76           (k6_relat_1 @ sk_A)))
% 54.47/54.76         <= (~
% 54.47/54.76             ((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 54.47/54.76                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 54.47/54.76               (k6_partfun1 @ sk_A))))),
% 54.47/54.76      inference('sup-', [status(thm)], ['85', '90'])).
% 54.47/54.76  thf('92', plain,
% 54.47/54.76      (![X0 : $i]:
% 54.47/54.76         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 54.47/54.76      inference('sup-', [status(thm)], ['72', '74'])).
% 54.47/54.76  thf('93', plain,
% 54.47/54.76      (((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 54.47/54.76          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 54.47/54.76         (k6_partfun1 @ sk_A)))),
% 54.47/54.76      inference('demod', [status(thm)], ['91', '92'])).
% 54.47/54.76  thf('94', plain,
% 54.47/54.76      (~
% 54.47/54.76       ((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 54.47/54.76          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 54.47/54.76         (k6_partfun1 @ sk_A))) | 
% 54.47/54.76       ~
% 54.47/54.76       ((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 54.47/54.76          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 54.47/54.76         (k6_partfun1 @ sk_A)))),
% 54.47/54.76      inference('split', [status(esa)], ['0'])).
% 54.47/54.76  thf('95', plain,
% 54.47/54.76      (~
% 54.47/54.76       ((r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 54.47/54.76          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 54.47/54.76         (k6_partfun1 @ sk_A)))),
% 54.47/54.76      inference('sat_resolution*', [status(thm)], ['93', '94'])).
% 54.47/54.76  thf('96', plain,
% 54.47/54.76      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 54.47/54.76          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 54.47/54.76          (k6_relat_1 @ sk_A))),
% 54.47/54.76      inference('simpl_trail', [status(thm)], ['11', '95'])).
% 54.47/54.76  thf('97', plain,
% 54.47/54.76      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 54.47/54.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 54.47/54.76  thf('98', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 54.47/54.76  thf('99', plain,
% 54.47/54.76      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 54.47/54.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('demod', [status(thm)], ['97', '98'])).
% 54.47/54.76  thf('100', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('101', plain,
% 54.47/54.76      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 54.47/54.76         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 54.47/54.76          | ~ (v1_funct_1 @ X32)
% 54.47/54.76          | ~ (v1_funct_1 @ X35)
% 54.47/54.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 54.47/54.76          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 54.47/54.76              = (k5_relat_1 @ X32 @ X35)))),
% 54.47/54.76      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 54.47/54.76  thf('102', plain,
% 54.47/54.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.47/54.76         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 54.47/54.76            = (k5_relat_1 @ sk_B @ X0))
% 54.47/54.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 54.47/54.76          | ~ (v1_funct_1 @ X0)
% 54.47/54.76          | ~ (v1_funct_1 @ sk_B))),
% 54.47/54.76      inference('sup-', [status(thm)], ['100', '101'])).
% 54.47/54.76  thf('103', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('104', plain,
% 54.47/54.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.47/54.76         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 54.47/54.76            = (k5_relat_1 @ sk_B @ X0))
% 54.47/54.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 54.47/54.76          | ~ (v1_funct_1 @ X0))),
% 54.47/54.76      inference('demod', [status(thm)], ['102', '103'])).
% 54.47/54.76  thf('105', plain,
% 54.47/54.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 54.47/54.76        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 54.47/54.76            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 54.47/54.76      inference('sup-', [status(thm)], ['99', '104'])).
% 54.47/54.76  thf('106', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 54.47/54.76  thf('107', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 54.47/54.76  thf('108', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['106', '107'])).
% 54.47/54.76  thf('109', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf(d1_funct_2, axiom,
% 54.47/54.76    (![A:$i,B:$i,C:$i]:
% 54.47/54.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.47/54.76       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 54.47/54.76           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 54.47/54.76             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 54.47/54.76         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 54.47/54.76           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 54.47/54.76             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 54.47/54.76  thf(zf_stmt_1, axiom,
% 54.47/54.76    (![C:$i,B:$i,A:$i]:
% 54.47/54.76     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 54.47/54.76       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 54.47/54.76  thf('110', plain,
% 54.47/54.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 54.47/54.76         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 54.47/54.76          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 54.47/54.76          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_1])).
% 54.47/54.76  thf('111', plain,
% 54.47/54.76      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 54.47/54.76        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 54.47/54.76      inference('sup-', [status(thm)], ['109', '110'])).
% 54.47/54.76  thf('112', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 54.47/54.76  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 54.47/54.76  thf(zf_stmt_4, axiom,
% 54.47/54.76    (![B:$i,A:$i]:
% 54.47/54.76     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 54.47/54.76       ( zip_tseitin_0 @ B @ A ) ))).
% 54.47/54.76  thf(zf_stmt_5, axiom,
% 54.47/54.76    (![A:$i,B:$i,C:$i]:
% 54.47/54.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.47/54.76       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 54.47/54.76         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 54.47/54.76           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 54.47/54.76             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 54.47/54.76  thf('113', plain,
% 54.47/54.76      (![X23 : $i, X24 : $i, X25 : $i]:
% 54.47/54.76         (~ (zip_tseitin_0 @ X23 @ X24)
% 54.47/54.76          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 54.47/54.76          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 54.47/54.76  thf('114', plain,
% 54.47/54.76      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 54.47/54.76      inference('sup-', [status(thm)], ['112', '113'])).
% 54.47/54.76  thf('115', plain,
% 54.47/54.76      (![X18 : $i, X19 : $i]:
% 54.47/54.76         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_4])).
% 54.47/54.76  thf('116', plain,
% 54.47/54.76      (![X18 : $i, X19 : $i]:
% 54.47/54.76         ((zip_tseitin_0 @ X18 @ X19) | ((X19) != (k1_xboole_0)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_4])).
% 54.47/54.76  thf('117', plain, (![X18 : $i]: (zip_tseitin_0 @ X18 @ k1_xboole_0)),
% 54.47/54.76      inference('simplify', [status(thm)], ['116'])).
% 54.47/54.76  thf('118', plain,
% 54.47/54.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.47/54.76         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 54.47/54.76      inference('sup+', [status(thm)], ['115', '117'])).
% 54.47/54.76  thf('119', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 54.47/54.76      inference('eq_fact', [status(thm)], ['118'])).
% 54.47/54.76  thf('120', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 54.47/54.76      inference('demod', [status(thm)], ['114', '119'])).
% 54.47/54.76  thf('121', plain,
% 54.47/54.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf(redefinition_k1_relset_1, axiom,
% 54.47/54.76    (![A:$i,B:$i,C:$i]:
% 54.47/54.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.47/54.76       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 54.47/54.76  thf('122', plain,
% 54.47/54.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 54.47/54.76         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 54.47/54.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 54.47/54.76      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 54.47/54.76  thf('123', plain,
% 54.47/54.76      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 54.47/54.76      inference('sup-', [status(thm)], ['121', '122'])).
% 54.47/54.76  thf('124', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['111', '120', '123'])).
% 54.47/54.76  thf('125', plain,
% 54.47/54.76      (![X1 : $i]:
% 54.47/54.76         (~ (v2_funct_1 @ X1)
% 54.47/54.76          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 54.47/54.76              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 54.47/54.76          | ~ (v1_funct_1 @ X1)
% 54.47/54.76          | ~ (v1_relat_1 @ X1))),
% 54.47/54.76      inference('cnf', [status(esa)], [t61_funct_1])).
% 54.47/54.76  thf('126', plain,
% 54.47/54.76      (![X31 : $i]:
% 54.47/54.76         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 54.47/54.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 54.47/54.76      inference('demod', [status(thm)], ['51', '52'])).
% 54.47/54.76  thf('127', plain,
% 54.47/54.76      (![X0 : $i]:
% 54.47/54.76         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 54.47/54.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 54.47/54.76          | ~ (v1_relat_1 @ X0)
% 54.47/54.76          | ~ (v1_funct_1 @ X0)
% 54.47/54.76          | ~ (v2_funct_1 @ X0))),
% 54.47/54.76      inference('sup+', [status(thm)], ['125', '126'])).
% 54.47/54.76  thf('128', plain,
% 54.47/54.76      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 54.47/54.76         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 54.47/54.76        | ~ (v2_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v1_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v1_relat_1 @ sk_B))),
% 54.47/54.76      inference('sup+', [status(thm)], ['124', '127'])).
% 54.47/54.76  thf('129', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['111', '120', '123'])).
% 54.47/54.76  thf('130', plain, ((v2_funct_1 @ sk_B)),
% 54.47/54.76      inference('demod', [status(thm)], ['59', '60', '61'])).
% 54.47/54.76  thf('131', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.76  thf('132', plain, ((v1_relat_1 @ sk_B)),
% 54.47/54.76      inference('sup-', [status(thm)], ['43', '44'])).
% 54.47/54.76  thf('133', plain,
% 54.47/54.76      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 54.47/54.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 54.47/54.76      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 54.47/54.76  thf('134', plain,
% 54.47/54.76      (![X0 : $i, X1 : $i]:
% 54.47/54.76         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 54.47/54.76          | ((k6_relat_1 @ X0) = (X1))
% 54.47/54.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 54.47/54.76      inference('sup-', [status(thm)], ['66', '67'])).
% 54.47/54.76  thf('135', plain,
% 54.47/54.76      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 54.47/54.76        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 54.47/54.76             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 54.47/54.76      inference('sup-', [status(thm)], ['133', '134'])).
% 54.47/54.76  thf('136', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 54.47/54.76      inference('demod', [status(thm)], ['111', '120', '123'])).
% 54.47/54.76  thf('137', plain,
% 54.47/54.76      (![X1 : $i]:
% 54.47/54.76         (~ (v2_funct_1 @ X1)
% 54.47/54.76          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 54.47/54.76              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 54.47/54.76          | ~ (v1_funct_1 @ X1)
% 54.47/54.76          | ~ (v1_relat_1 @ X1))),
% 54.47/54.76      inference('cnf', [status(esa)], [t61_funct_1])).
% 54.47/54.76  thf('138', plain,
% 54.47/54.76      (![X0 : $i]:
% 54.47/54.76         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 54.47/54.76      inference('sup-', [status(thm)], ['72', '74'])).
% 54.47/54.76  thf('139', plain,
% 54.47/54.76      (![X0 : $i]:
% 54.47/54.76         ((r2_relset_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 54.47/54.76           (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 54.47/54.76           (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 54.47/54.76          | ~ (v1_relat_1 @ X0)
% 54.47/54.76          | ~ (v1_funct_1 @ X0)
% 54.47/54.76          | ~ (v2_funct_1 @ X0))),
% 54.47/54.76      inference('sup+', [status(thm)], ['137', '138'])).
% 54.47/54.76  thf('140', plain,
% 54.47/54.76      (((r2_relset_1 @ sk_A @ (k1_relat_1 @ sk_B) @ 
% 54.47/54.76         (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 54.47/54.76         (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 54.47/54.76        | ~ (v2_funct_1 @ sk_B)
% 54.47/54.76        | ~ (v1_funct_1 @ sk_B)
% 54.47/54.77        | ~ (v1_relat_1 @ sk_B))),
% 54.47/54.77      inference('sup+', [status(thm)], ['136', '139'])).
% 54.47/54.77  thf('141', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 54.47/54.77      inference('demod', [status(thm)], ['111', '120', '123'])).
% 54.47/54.77  thf('142', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 54.47/54.77      inference('demod', [status(thm)], ['111', '120', '123'])).
% 54.47/54.77  thf('143', plain, ((v2_funct_1 @ sk_B)),
% 54.47/54.77      inference('demod', [status(thm)], ['59', '60', '61'])).
% 54.47/54.77  thf('144', plain, ((v1_funct_1 @ sk_B)),
% 54.47/54.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.47/54.77  thf('145', plain, ((v1_relat_1 @ sk_B)),
% 54.47/54.77      inference('sup-', [status(thm)], ['43', '44'])).
% 54.47/54.77  thf('146', plain,
% 54.47/54.77      ((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 54.47/54.77        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 54.47/54.77      inference('demod', [status(thm)],
% 54.47/54.77                ['140', '141', '142', '143', '144', '145'])).
% 54.47/54.77  thf('147', plain,
% 54.47/54.77      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 54.47/54.77      inference('demod', [status(thm)], ['135', '146'])).
% 54.47/54.77  thf('148', plain,
% 54.47/54.77      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 54.47/54.77         = (k6_relat_1 @ sk_A))),
% 54.47/54.77      inference('demod', [status(thm)], ['105', '108', '147'])).
% 54.47/54.77  thf('149', plain,
% 54.47/54.77      (![X0 : $i]:
% 54.47/54.77         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 54.47/54.77      inference('sup-', [status(thm)], ['72', '74'])).
% 54.47/54.77  thf('150', plain, ($false),
% 54.47/54.77      inference('demod', [status(thm)], ['96', '148', '149'])).
% 54.47/54.77  
% 54.47/54.77  % SZS output end Refutation
% 54.47/54.77  
% 54.47/54.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
