%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DeagnyJixY

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:05 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  224 (1048 expanded)
%              Number of leaves         :   46 ( 335 expanded)
%              Depth                    :   17
%              Number of atoms          : 2081 (23855 expanded)
%              Number of equality atoms :  154 ( 467 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X34: $i,X35: $i] :
      ( ( ( k2_funct_2 @ X35 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v3_funct_2 @ X34 @ X35 @ X35 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( X41
        = ( k2_funct_1 @ X44 ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41 ) @ ( k6_partfun1 @ X43 ) )
      | ( X42 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
       != X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('30',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( X41
        = ( k2_funct_1 @ X44 ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41 ) @ ( k6_relat_1 @ X43 ) )
      | ( X42 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
       != X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('50',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['55','58','61'])).

thf('63',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['47','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('66',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','41','42','43','44','63','69'])).

thf('71',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('73',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('76',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf('79',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('82',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('93',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['87','90','93'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('95',plain,(
    ! [X3: $i] :
      ( ( ( k2_relat_1 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('96',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('98',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf('100',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['55','58','61'])).

thf('103',plain,(
    ! [X3: $i] :
      ( ( ( k2_relat_1 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('104',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('106',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf('108',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['108'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('110',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('111',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('112',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('115',plain,(
    ! [X2: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X2 ) @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('117',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

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

thf('122',plain,(
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

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('129',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X1 )
        = ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['119','130'])).

thf('132',plain,
    ( ( ( k2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ k1_xboole_0 ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) )
      = ( k2_funct_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) )
    | ( ( k6_relat_1 @ k1_xboole_0 )
     != ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','131'])).

thf('133',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('134',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('135',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('137',plain,
    ( ( k2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('138',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('139',plain,
    ( ( k2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('141',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('142',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('143',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('144',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('145',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('146',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('147',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('148',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('149',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('150',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('151',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('152',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('153',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('154',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('155',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('156',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','139','140','141','142','143','144','145','146','147','148','149','150','151','152','153','154','155'])).

thf('157',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['158','163'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('168',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf('170',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('171',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['157','171'])).

thf('173',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('174',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('175',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    $false ),
    inference(demod,[status(thm)],['79','101','109','172','175'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DeagnyJixY
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:15:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.75/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.95  % Solved by: fo/fo7.sh
% 0.75/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.95  % done 471 iterations in 0.459s
% 0.75/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.95  % SZS output start Refutation
% 0.75/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.95  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.75/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.95  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.75/0.95  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.95  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.75/0.95  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.75/0.95  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.75/0.95  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.75/0.95  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.75/0.95  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.75/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.95  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.75/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.95  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.75/0.95  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.75/0.95  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.75/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.95  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.75/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.95  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.75/0.95  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.75/0.95  thf(t87_funct_2, conjecture,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.75/0.95         ( v3_funct_2 @ B @ A @ A ) & 
% 0.75/0.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.75/0.95       ( ![C:$i]:
% 0.75/0.95         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.75/0.95             ( v3_funct_2 @ C @ A @ A ) & 
% 0.75/0.95             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.75/0.95           ( ( r2_relset_1 @
% 0.75/0.95               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.75/0.95               ( k6_partfun1 @ A ) ) =>
% 0.75/0.95             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.75/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.95    (~( ![A:$i,B:$i]:
% 0.75/0.95        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.75/0.95            ( v3_funct_2 @ B @ A @ A ) & 
% 0.75/0.95            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.75/0.95          ( ![C:$i]:
% 0.75/0.95            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.75/0.95                ( v3_funct_2 @ C @ A @ A ) & 
% 0.75/0.95                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.75/0.95              ( ( r2_relset_1 @
% 0.75/0.95                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.75/0.95                  ( k6_partfun1 @ A ) ) =>
% 0.75/0.95                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.75/0.95    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.75/0.95  thf('0', plain,
% 0.75/0.95      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('1', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(redefinition_k2_funct_2, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.75/0.95         ( v3_funct_2 @ B @ A @ A ) & 
% 0.75/0.95         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.75/0.95       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.75/0.95  thf('2', plain,
% 0.75/0.95      (![X34 : $i, X35 : $i]:
% 0.75/0.95         (((k2_funct_2 @ X35 @ X34) = (k2_funct_1 @ X34))
% 0.75/0.95          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.75/0.95          | ~ (v3_funct_2 @ X34 @ X35 @ X35)
% 0.75/0.95          | ~ (v1_funct_2 @ X34 @ X35 @ X35)
% 0.75/0.95          | ~ (v1_funct_1 @ X34))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.75/0.95  thf('3', plain,
% 0.75/0.95      ((~ (v1_funct_1 @ sk_B)
% 0.75/0.95        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.75/0.95        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.75/0.95        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.95  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.75/0.95      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.75/0.95  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.75/0.95      inference('demod', [status(thm)], ['0', '7'])).
% 0.75/0.95  thf('9', plain,
% 0.75/0.95      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.95        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.75/0.95        (k6_partfun1 @ sk_A))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(redefinition_k6_partfun1, axiom,
% 0.75/0.95    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.75/0.95  thf('10', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.95  thf('11', plain,
% 0.75/0.95      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.95        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.75/0.95        (k6_relat_1 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.95  thf('12', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('13', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(dt_k1_partfun1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.95     ( ( ( v1_funct_1 @ E ) & 
% 0.75/0.95         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.95         ( v1_funct_1 @ F ) & 
% 0.75/0.95         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.75/0.95       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.75/0.95         ( m1_subset_1 @
% 0.75/0.95           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.75/0.95           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.75/0.95  thf('14', plain,
% 0.75/0.95      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.75/0.95          | ~ (v1_funct_1 @ X26)
% 0.75/0.95          | ~ (v1_funct_1 @ X29)
% 0.75/0.95          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.75/0.95          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 0.75/0.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.75/0.95  thf('15', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.75/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.75/0.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.75/0.95          | ~ (v1_funct_1 @ X1)
% 0.75/0.95          | ~ (v1_funct_1 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.95  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('17', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.75/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.75/0.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.75/0.95          | ~ (v1_funct_1 @ X1))),
% 0.75/0.95      inference('demod', [status(thm)], ['15', '16'])).
% 0.75/0.95  thf('18', plain,
% 0.75/0.95      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.95        | (m1_subset_1 @ 
% 0.75/0.95           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.75/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['12', '17'])).
% 0.75/0.95  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('20', plain,
% 0.75/0.95      ((m1_subset_1 @ 
% 0.75/0.95        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.75/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('demod', [status(thm)], ['18', '19'])).
% 0.75/0.95  thf(redefinition_r2_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.95     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.95       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.75/0.95  thf('21', plain,
% 0.75/0.95      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.75/0.95          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.75/0.95          | ((X17) = (X20))
% 0.75/0.95          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.75/0.95  thf('22', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.95             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 0.75/0.95          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 0.75/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['20', '21'])).
% 0.75/0.95  thf('23', plain,
% 0.75/0.95      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.75/0.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.75/0.95        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.75/0.95            = (k6_relat_1 @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['11', '22'])).
% 0.75/0.95  thf(dt_k6_partfun1, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( m1_subset_1 @
% 0.75/0.95         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.75/0.95       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.75/0.95  thf('24', plain,
% 0.75/0.95      (![X33 : $i]:
% 0.75/0.95         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 0.75/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.75/0.95  thf('25', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.95  thf('26', plain,
% 0.75/0.95      (![X33 : $i]:
% 0.75/0.95         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 0.75/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.75/0.95      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.95  thf('27', plain,
% 0.75/0.95      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.75/0.95         = (k6_relat_1 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['23', '26'])).
% 0.75/0.95  thf('28', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(t36_funct_2, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.95       ( ![D:$i]:
% 0.75/0.95         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.75/0.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.75/0.95           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.75/0.95               ( r2_relset_1 @
% 0.75/0.95                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.75/0.95                 ( k6_partfun1 @ A ) ) & 
% 0.75/0.95               ( v2_funct_1 @ C ) ) =>
% 0.75/0.95             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.75/0.95               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.75/0.95  thf('29', plain,
% 0.75/0.95      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.75/0.95         (~ (v1_funct_1 @ X41)
% 0.75/0.95          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.75/0.95          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.75/0.95          | ((X41) = (k2_funct_1 @ X44))
% 0.75/0.95          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 0.75/0.95               (k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41) @ 
% 0.75/0.95               (k6_partfun1 @ X43))
% 0.75/0.95          | ((X42) = (k1_xboole_0))
% 0.75/0.95          | ((X43) = (k1_xboole_0))
% 0.75/0.95          | ~ (v2_funct_1 @ X44)
% 0.75/0.95          | ((k2_relset_1 @ X43 @ X42 @ X44) != (X42))
% 0.75/0.95          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.75/0.95          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 0.75/0.95          | ~ (v1_funct_1 @ X44))),
% 0.75/0.95      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.75/0.95  thf('30', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.95  thf('31', plain,
% 0.75/0.95      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.75/0.95         (~ (v1_funct_1 @ X41)
% 0.75/0.95          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.75/0.95          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.75/0.95          | ((X41) = (k2_funct_1 @ X44))
% 0.75/0.95          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 0.75/0.95               (k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41) @ 
% 0.75/0.95               (k6_relat_1 @ X43))
% 0.75/0.95          | ((X42) = (k1_xboole_0))
% 0.75/0.95          | ((X43) = (k1_xboole_0))
% 0.75/0.95          | ~ (v2_funct_1 @ X44)
% 0.75/0.95          | ((k2_relset_1 @ X43 @ X42 @ X44) != (X42))
% 0.75/0.95          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.75/0.95          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 0.75/0.95          | ~ (v1_funct_1 @ X44))),
% 0.75/0.95      inference('demod', [status(thm)], ['29', '30'])).
% 0.75/0.95  thf('32', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (v1_funct_1 @ X0)
% 0.75/0.95          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.75/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.75/0.95          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.75/0.95          | ~ (v2_funct_1 @ X0)
% 0.75/0.95          | ((sk_A) = (k1_xboole_0))
% 0.75/0.95          | ((sk_A) = (k1_xboole_0))
% 0.75/0.95          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.95               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.75/0.95               (k6_relat_1 @ sk_A))
% 0.75/0.95          | ((sk_C) = (k2_funct_1 @ X0))
% 0.75/0.95          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.75/0.95          | ~ (v1_funct_1 @ sk_C))),
% 0.75/0.95      inference('sup-', [status(thm)], ['28', '31'])).
% 0.75/0.95  thf('33', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('35', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (v1_funct_1 @ X0)
% 0.75/0.95          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.75/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.75/0.95          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.75/0.95          | ~ (v2_funct_1 @ X0)
% 0.75/0.95          | ((sk_A) = (k1_xboole_0))
% 0.75/0.95          | ((sk_A) = (k1_xboole_0))
% 0.75/0.95          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.95               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.75/0.95               (k6_relat_1 @ sk_A))
% 0.75/0.95          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.75/0.95  thf('36', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (((sk_C) = (k2_funct_1 @ X0))
% 0.75/0.95          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.95               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.75/0.95               (k6_relat_1 @ sk_A))
% 0.75/0.95          | ((sk_A) = (k1_xboole_0))
% 0.75/0.95          | ~ (v2_funct_1 @ X0)
% 0.75/0.95          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.75/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.75/0.95          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.75/0.95          | ~ (v1_funct_1 @ X0))),
% 0.75/0.95      inference('simplify', [status(thm)], ['35'])).
% 0.75/0.95  thf('37', plain,
% 0.75/0.95      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.75/0.95           (k6_relat_1 @ sk_A))
% 0.75/0.95        | ~ (v1_funct_1 @ sk_B)
% 0.75/0.95        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.75/0.95        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.75/0.95        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.75/0.95        | ~ (v2_funct_1 @ sk_B)
% 0.75/0.95        | ((sk_A) = (k1_xboole_0))
% 0.75/0.95        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['27', '36'])).
% 0.75/0.95  thf('38', plain,
% 0.75/0.95      (![X33 : $i]:
% 0.75/0.95         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 0.75/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.75/0.95      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.95  thf('39', plain,
% 0.75/0.95      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.75/0.95          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.75/0.95          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 0.75/0.95          | ((X17) != (X20)))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.75/0.95  thf('40', plain,
% 0.75/0.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.75/0.95         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.75/0.95          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.75/0.95      inference('simplify', [status(thm)], ['39'])).
% 0.75/0.95  thf('41', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['38', '40'])).
% 0.75/0.95  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('43', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('44', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('45', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(redefinition_k2_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.75/0.95  thf('46', plain,
% 0.75/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.95         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.75/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.95  thf('47', plain,
% 0.75/0.95      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.95  thf('48', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(cc2_funct_2, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.75/0.95         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.75/0.95  thf('49', plain,
% 0.75/0.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.75/0.95         (~ (v1_funct_1 @ X21)
% 0.75/0.95          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.75/0.95          | (v2_funct_2 @ X21 @ X23)
% 0.75/0.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.75/0.95  thf('50', plain,
% 0.75/0.95      (((v2_funct_2 @ sk_B @ sk_A)
% 0.75/0.95        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.75/0.95        | ~ (v1_funct_1 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['48', '49'])).
% 0.75/0.95  thf('51', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('52', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('53', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.75/0.95      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.75/0.95  thf(d3_funct_2, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.75/0.95       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.75/0.95  thf('54', plain,
% 0.75/0.95      (![X24 : $i, X25 : $i]:
% 0.75/0.95         (~ (v2_funct_2 @ X25 @ X24)
% 0.75/0.95          | ((k2_relat_1 @ X25) = (X24))
% 0.75/0.95          | ~ (v5_relat_1 @ X25 @ X24)
% 0.75/0.95          | ~ (v1_relat_1 @ X25))),
% 0.75/0.95      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.75/0.95  thf('55', plain,
% 0.75/0.95      ((~ (v1_relat_1 @ sk_B)
% 0.75/0.95        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.75/0.95        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.95  thf('56', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(cc1_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( v1_relat_1 @ C ) ))).
% 0.75/0.95  thf('57', plain,
% 0.75/0.95      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.75/0.95         ((v1_relat_1 @ X8)
% 0.75/0.95          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.95  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.95      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.95  thf('59', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(cc2_relset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.75/0.95  thf('60', plain,
% 0.75/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.95         ((v5_relat_1 @ X11 @ X13)
% 0.75/0.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.95  thf('61', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.75/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.75/0.95  thf('62', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['55', '58', '61'])).
% 0.75/0.95  thf('63', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['47', '62'])).
% 0.75/0.95  thf('64', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('65', plain,
% 0.75/0.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.75/0.95         (~ (v1_funct_1 @ X21)
% 0.75/0.95          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.75/0.95          | (v2_funct_1 @ X21)
% 0.75/0.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.75/0.95  thf('66', plain,
% 0.75/0.95      (((v2_funct_1 @ sk_B)
% 0.75/0.95        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.75/0.95        | ~ (v1_funct_1 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['64', '65'])).
% 0.75/0.95  thf('67', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('69', plain, ((v2_funct_1 @ sk_B)),
% 0.75/0.95      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.75/0.95  thf('70', plain,
% 0.75/0.95      ((((sk_A) != (sk_A))
% 0.75/0.95        | ((sk_A) = (k1_xboole_0))
% 0.75/0.95        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.75/0.95      inference('demod', [status(thm)],
% 0.75/0.95                ['37', '41', '42', '43', '44', '63', '69'])).
% 0.75/0.95  thf('71', plain,
% 0.75/0.95      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['70'])).
% 0.75/0.95  thf('72', plain,
% 0.75/0.95      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.75/0.95      inference('demod', [status(thm)], ['0', '7'])).
% 0.75/0.95  thf('73', plain,
% 0.75/0.95      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['71', '72'])).
% 0.75/0.95  thf('74', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('75', plain,
% 0.75/0.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.75/0.95         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.75/0.95          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.75/0.95      inference('simplify', [status(thm)], ['39'])).
% 0.75/0.95  thf('76', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.75/0.95      inference('sup-', [status(thm)], ['74', '75'])).
% 0.75/0.95  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 0.75/0.95      inference('demod', [status(thm)], ['73', '76'])).
% 0.75/0.95  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 0.75/0.95      inference('demod', [status(thm)], ['73', '76'])).
% 0.75/0.95  thf('79', plain,
% 0.75/0.95      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.75/0.95      inference('demod', [status(thm)], ['8', '77', '78'])).
% 0.75/0.95  thf('80', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('81', plain,
% 0.75/0.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.75/0.95         (~ (v1_funct_1 @ X21)
% 0.75/0.95          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 0.75/0.95          | (v2_funct_2 @ X21 @ X23)
% 0.75/0.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.75/0.95  thf('82', plain,
% 0.75/0.95      (((v2_funct_2 @ sk_C @ sk_A)
% 0.75/0.95        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.75/0.95        | ~ (v1_funct_1 @ sk_C))),
% 0.75/0.95      inference('sup-', [status(thm)], ['80', '81'])).
% 0.75/0.95  thf('83', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('85', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.75/0.95      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.75/0.95  thf('86', plain,
% 0.75/0.95      (![X24 : $i, X25 : $i]:
% 0.75/0.95         (~ (v2_funct_2 @ X25 @ X24)
% 0.75/0.95          | ((k2_relat_1 @ X25) = (X24))
% 0.75/0.95          | ~ (v5_relat_1 @ X25 @ X24)
% 0.75/0.95          | ~ (v1_relat_1 @ X25))),
% 0.75/0.95      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.75/0.95  thf('87', plain,
% 0.75/0.95      ((~ (v1_relat_1 @ sk_C)
% 0.75/0.95        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.75/0.95        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['85', '86'])).
% 0.75/0.95  thf('88', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('89', plain,
% 0.75/0.95      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.75/0.95         ((v1_relat_1 @ X8)
% 0.75/0.95          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.95  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.95      inference('sup-', [status(thm)], ['88', '89'])).
% 0.75/0.95  thf('91', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('92', plain,
% 0.75/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.95         ((v5_relat_1 @ X11 @ X13)
% 0.75/0.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.75/0.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.95  thf('93', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.75/0.95      inference('sup-', [status(thm)], ['91', '92'])).
% 0.75/0.95  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['87', '90', '93'])).
% 0.75/0.95  thf(t64_relat_1, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( v1_relat_1 @ A ) =>
% 0.75/0.95       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.95           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.95         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.75/0.95  thf('95', plain,
% 0.75/0.95      (![X3 : $i]:
% 0.75/0.95         (((k2_relat_1 @ X3) != (k1_xboole_0))
% 0.75/0.95          | ((X3) = (k1_xboole_0))
% 0.75/0.95          | ~ (v1_relat_1 @ X3))),
% 0.75/0.95      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.75/0.95  thf('96', plain,
% 0.75/0.95      ((((sk_A) != (k1_xboole_0))
% 0.75/0.95        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.95        | ((sk_C) = (k1_xboole_0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['94', '95'])).
% 0.75/0.95  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.95      inference('sup-', [status(thm)], ['88', '89'])).
% 0.75/0.95  thf('98', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['96', '97'])).
% 0.75/0.95  thf('99', plain, (((sk_A) = (k1_xboole_0))),
% 0.75/0.95      inference('demod', [status(thm)], ['73', '76'])).
% 0.75/0.95  thf('100', plain,
% 0.75/0.95      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['98', '99'])).
% 0.75/0.95  thf('101', plain, (((sk_C) = (k1_xboole_0))),
% 0.75/0.95      inference('simplify', [status(thm)], ['100'])).
% 0.75/0.95  thf('102', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['55', '58', '61'])).
% 0.75/0.95  thf('103', plain,
% 0.75/0.95      (![X3 : $i]:
% 0.75/0.95         (((k2_relat_1 @ X3) != (k1_xboole_0))
% 0.75/0.95          | ((X3) = (k1_xboole_0))
% 0.75/0.95          | ~ (v1_relat_1 @ X3))),
% 0.75/0.95      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.75/0.95  thf('104', plain,
% 0.75/0.95      ((((sk_A) != (k1_xboole_0))
% 0.75/0.95        | ~ (v1_relat_1 @ sk_B)
% 0.75/0.95        | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['102', '103'])).
% 0.75/0.95  thf('105', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.95      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.95  thf('106', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['104', '105'])).
% 0.75/0.95  thf('107', plain, (((sk_A) = (k1_xboole_0))),
% 0.75/0.95      inference('demod', [status(thm)], ['73', '76'])).
% 0.75/0.95  thf('108', plain,
% 0.75/0.95      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['106', '107'])).
% 0.75/0.95  thf('109', plain, (((sk_B) = (k1_xboole_0))),
% 0.75/0.95      inference('simplify', [status(thm)], ['108'])).
% 0.75/0.95  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.75/0.95  thf('110', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('111', plain,
% 0.75/0.95      (![X33 : $i]:
% 0.75/0.95         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 0.75/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.75/0.95      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.95  thf('112', plain,
% 0.75/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.95         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.75/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.95  thf('113', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((k2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0))
% 0.75/0.95           = (k2_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['111', '112'])).
% 0.75/0.95  thf('114', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((k2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0))
% 0.75/0.95           = (k2_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['111', '112'])).
% 0.75/0.95  thf(t126_relat_1, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( v1_relat_1 @ A ) =>
% 0.75/0.95       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.75/0.95  thf('115', plain,
% 0.75/0.95      (![X2 : $i]:
% 0.75/0.95         (((k8_relat_1 @ (k2_relat_1 @ X2) @ X2) = (X2)) | ~ (v1_relat_1 @ X2))),
% 0.75/0.95      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.75/0.95  thf('116', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (((k8_relat_1 @ (k2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0)) @ 
% 0.75/0.95            (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.75/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('sup+', [status(thm)], ['114', '115'])).
% 0.75/0.95  thf(fc4_funct_1, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.75/0.95       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.75/0.95  thf('117', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.75/0.95      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.75/0.95  thf('118', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((k8_relat_1 @ (k2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0)) @ 
% 0.75/0.95           (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.75/0.95      inference('demod', [status(thm)], ['116', '117'])).
% 0.75/0.95  thf('119', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((k8_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ (k6_relat_1 @ X0))
% 0.75/0.95           = (k6_relat_1 @ X0))),
% 0.75/0.95      inference('sup+', [status(thm)], ['113', '118'])).
% 0.75/0.95  thf('120', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((k2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0))
% 0.75/0.95           = (k2_relat_1 @ (k6_relat_1 @ X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['111', '112'])).
% 0.75/0.95  thf(t123_relat_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( v1_relat_1 @ B ) =>
% 0.75/0.95       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.75/0.95  thf('121', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k8_relat_1 @ X1 @ X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.75/0.95          | ~ (v1_relat_1 @ X0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.75/0.95  thf(t63_funct_1, axiom,
% 0.75/0.95    (![A:$i]:
% 0.75/0.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.95       ( ![B:$i]:
% 0.75/0.95         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.75/0.95           ( ( ( v2_funct_1 @ A ) & 
% 0.75/0.95               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.75/0.95               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.75/0.95             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.75/0.95  thf('122', plain,
% 0.75/0.95      (![X6 : $i, X7 : $i]:
% 0.75/0.95         (~ (v1_relat_1 @ X6)
% 0.75/0.95          | ~ (v1_funct_1 @ X6)
% 0.75/0.95          | ((X6) = (k2_funct_1 @ X7))
% 0.75/0.95          | ((k5_relat_1 @ X7 @ X6) != (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.75/0.95          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X6))
% 0.75/0.95          | ~ (v2_funct_1 @ X7)
% 0.75/0.95          | ~ (v1_funct_1 @ X7)
% 0.75/0.95          | ~ (v1_relat_1 @ X7))),
% 0.75/0.95      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.75/0.95  thf('123', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k8_relat_1 @ X1 @ X0) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.75/0.95          | ~ (v1_relat_1 @ X0)
% 0.75/0.95          | ~ (v1_relat_1 @ X0)
% 0.75/0.95          | ~ (v1_funct_1 @ X0)
% 0.75/0.95          | ~ (v2_funct_1 @ X0)
% 0.75/0.95          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k6_relat_1 @ X1)))
% 0.75/0.95          | ((k6_relat_1 @ X1) = (k2_funct_1 @ X0))
% 0.75/0.95          | ~ (v1_funct_1 @ (k6_relat_1 @ X1))
% 0.75/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['121', '122'])).
% 0.75/0.95  thf('124', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.75/0.95      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.75/0.95  thf('125', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k8_relat_1 @ X1 @ X0) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.75/0.95          | ~ (v1_relat_1 @ X0)
% 0.75/0.95          | ~ (v1_relat_1 @ X0)
% 0.75/0.95          | ~ (v1_funct_1 @ X0)
% 0.75/0.95          | ~ (v2_funct_1 @ X0)
% 0.75/0.95          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k6_relat_1 @ X1)))
% 0.75/0.95          | ((k6_relat_1 @ X1) = (k2_funct_1 @ X0))
% 0.75/0.95          | ~ (v1_funct_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.95      inference('demod', [status(thm)], ['123', '124'])).
% 0.75/0.95  thf('126', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (v1_funct_1 @ (k6_relat_1 @ X1))
% 0.75/0.95          | ((k6_relat_1 @ X1) = (k2_funct_1 @ X0))
% 0.75/0.95          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k6_relat_1 @ X1)))
% 0.75/0.95          | ~ (v2_funct_1 @ X0)
% 0.75/0.95          | ~ (v1_funct_1 @ X0)
% 0.75/0.95          | ~ (v1_relat_1 @ X0)
% 0.75/0.95          | ((k8_relat_1 @ X1 @ X0) != (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 0.75/0.95      inference('simplify', [status(thm)], ['125'])).
% 0.75/0.95  thf('127', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0))
% 0.75/0.95            != (k1_relat_1 @ (k6_relat_1 @ X1)))
% 0.75/0.95          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.75/0.95              != (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.75/0.95          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.75/0.95          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.75/0.95          | ~ (v2_funct_1 @ (k6_relat_1 @ X0))
% 0.75/0.95          | ((k6_relat_1 @ X1) = (k2_funct_1 @ (k6_relat_1 @ X0)))
% 0.75/0.95          | ~ (v1_funct_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['120', '126'])).
% 0.75/0.95  thf('128', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.75/0.95      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.75/0.95  thf('129', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 0.75/0.95      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.75/0.95  thf('130', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0))
% 0.75/0.95            != (k1_relat_1 @ (k6_relat_1 @ X1)))
% 0.75/0.95          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.75/0.95              != (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.75/0.95          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.75/0.95          | ((k6_relat_1 @ X1) = (k2_funct_1 @ (k6_relat_1 @ X0)))
% 0.75/0.95          | ~ (v1_funct_1 @ (k6_relat_1 @ X1)))),
% 0.75/0.95      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.75/0.95  thf('131', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (((k6_relat_1 @ X0) != (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.75/0.95          | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.75/0.95          | ((k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.75/0.95              = (k2_funct_1 @ (k6_relat_1 @ X0)))
% 0.75/0.95          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.75/0.95          | ((k2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0))
% 0.75/0.95              != (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['119', '130'])).
% 0.75/0.95  thf('132', plain,
% 0.75/0.95      ((((k2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.75/0.95          != (k1_relat_1 @ 
% 0.75/0.95              (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ k1_xboole_0)))))
% 0.75/0.95        | ~ (v1_funct_1 @ (k6_relat_1 @ k1_xboole_0))
% 0.75/0.95        | ((k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ k1_xboole_0)))
% 0.75/0.95            = (k2_funct_1 @ (k6_relat_1 @ k1_xboole_0)))
% 0.75/0.95        | ~ (v1_funct_1 @ 
% 0.75/0.95             (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ k1_xboole_0))))
% 0.75/0.95        | ((k6_relat_1 @ k1_xboole_0)
% 0.75/0.95            != (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ k1_xboole_0)))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['110', '131'])).
% 0.75/0.95  thf('133', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('134', plain,
% 0.75/0.95      (![X33 : $i]:
% 0.75/0.95         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 0.75/0.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.75/0.95      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.95  thf('135', plain,
% 0.75/0.95      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.75/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.75/0.95      inference('sup+', [status(thm)], ['133', '134'])).
% 0.75/0.95  thf('136', plain,
% 0.75/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.95         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.75/0.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.75/0.95      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.95  thf('137', plain,
% 0.75/0.95      (((k2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.75/0.95         = (k2_relat_1 @ k1_xboole_0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['135', '136'])).
% 0.75/0.95  thf(t60_relat_1, axiom,
% 0.75/0.95    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.75/0.95     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.75/0.95  thf('138', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.95  thf('139', plain,
% 0.75/0.95      (((k2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('demod', [status(thm)], ['137', '138'])).
% 0.75/0.95  thf('140', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('141', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.95  thf('142', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('143', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.95  thf('144', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('145', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('146', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.95  thf('147', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('148', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('149', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('150', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.95  thf('151', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('152', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('153', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('154', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.95  thf('155', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('156', plain,
% 0.75/0.95      ((((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.95        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.75/0.95        | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 0.75/0.95        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.75/0.95        | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.75/0.95      inference('demod', [status(thm)],
% 0.75/0.95                ['132', '139', '140', '141', '142', '143', '144', '145', 
% 0.75/0.95                 '146', '147', '148', '149', '150', '151', '152', '153', 
% 0.75/0.95                 '154', '155'])).
% 0.75/0.95  thf('157', plain,
% 0.75/0.95      ((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 0.75/0.95        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.75/0.95      inference('simplify', [status(thm)], ['156'])).
% 0.75/0.95  thf('158', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('159', plain,
% 0.75/0.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('160', plain,
% 0.75/0.95      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.75/0.95          | ~ (v1_funct_1 @ X26)
% 0.75/0.95          | ~ (v1_funct_1 @ X29)
% 0.75/0.95          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.75/0.95          | (v1_funct_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)))),
% 0.75/0.95      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.75/0.95  thf('161', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 0.75/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.75/0.95          | ~ (v1_funct_1 @ X0)
% 0.75/0.95          | ~ (v1_funct_1 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['159', '160'])).
% 0.75/0.95  thf('162', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('163', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 0.75/0.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.75/0.95          | ~ (v1_funct_1 @ X0))),
% 0.75/0.95      inference('demod', [status(thm)], ['161', '162'])).
% 0.75/0.95  thf('164', plain,
% 0.75/0.95      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.95        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['158', '163'])).
% 0.75/0.95  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('166', plain,
% 0.75/0.95      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C))),
% 0.75/0.95      inference('demod', [status(thm)], ['164', '165'])).
% 0.75/0.95  thf('167', plain,
% 0.75/0.95      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.75/0.95         = (k6_relat_1 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['23', '26'])).
% 0.75/0.95  thf('168', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['166', '167'])).
% 0.75/0.95  thf('169', plain, (((sk_A) = (k1_xboole_0))),
% 0.75/0.95      inference('demod', [status(thm)], ['73', '76'])).
% 0.75/0.95  thf('170', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.75/0.95  thf('171', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.75/0.95      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.75/0.95  thf('172', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.75/0.95      inference('demod', [status(thm)], ['157', '171'])).
% 0.75/0.95  thf('173', plain,
% 0.75/0.95      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.75/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.75/0.95      inference('sup+', [status(thm)], ['133', '134'])).
% 0.75/0.95  thf('174', plain,
% 0.75/0.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.75/0.95         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.75/0.95          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.75/0.95      inference('simplify', [status(thm)], ['39'])).
% 0.75/0.95  thf('175', plain,
% 0.75/0.95      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.75/0.95      inference('sup-', [status(thm)], ['173', '174'])).
% 0.75/0.95  thf('176', plain, ($false),
% 0.75/0.95      inference('demod', [status(thm)], ['79', '101', '109', '172', '175'])).
% 0.75/0.95  
% 0.75/0.95  % SZS output end Refutation
% 0.75/0.95  
% 0.75/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
