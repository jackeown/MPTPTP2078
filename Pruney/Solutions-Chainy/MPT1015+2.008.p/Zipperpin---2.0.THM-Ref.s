%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kMQauM1g36

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:48 EST 2020

% Result     : Theorem 1.11s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 203 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          : 1058 (4239 expanded)
%              Number of equality atoms :   58 (  73 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t76_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
              & ( v2_funct_1 @ B ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
                & ( v2_funct_1 @ B ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X41 @ X42 )
        = X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X41 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','31','34'])).

thf(t50_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = A )
              & ( ( k1_relat_1 @ C )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
              & ( v2_funct_1 @ B )
              & ( ( k5_relat_1 @ C @ B )
                = B ) )
           => ( C
              = ( k6_relat_1 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k6_relat_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X11 )
       != X11 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k1_relat_1 @ X9 )
       != X10 )
      | ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
       != X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t50_funct_1])).

thf('37',plain,(
    ! [X9: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( ( k5_relat_1 @ X9 @ X11 )
       != X11 )
      | ( X9
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_C
        = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','31','34'])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','31','34'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ( sk_C
        = ( k6_relat_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','41','42','43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('48',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k6_relat_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','54'])).

thf('56',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_C
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X41 @ X41 @ X42 )
        = X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X41 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('68',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['63','64','65','68'])).

thf('70',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_B != sk_B )
    | ( sk_A != sk_A )
    | ( sk_C
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59','60','69','70'])).

thf('72',plain,
    ( sk_C
    = ( k6_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('75',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['2','72','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kMQauM1g36
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.11/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.11/1.34  % Solved by: fo/fo7.sh
% 1.11/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.11/1.34  % done 969 iterations in 0.885s
% 1.11/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.11/1.34  % SZS output start Refutation
% 1.11/1.34  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.11/1.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.11/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.11/1.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.11/1.34  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.11/1.34  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.11/1.34  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.11/1.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.11/1.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.11/1.34  thf(sk_B_type, type, sk_B: $i).
% 1.11/1.34  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.11/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.11/1.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.11/1.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.11/1.34  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.11/1.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.11/1.34  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.11/1.34  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.11/1.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.11/1.34  thf(sk_C_type, type, sk_C: $i).
% 1.11/1.34  thf(t76_funct_2, conjecture,
% 1.11/1.34    (![A:$i,B:$i]:
% 1.11/1.34     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.11/1.34         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.11/1.34       ( ![C:$i]:
% 1.11/1.34         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.11/1.34             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.11/1.34           ( ( ( r2_relset_1 @
% 1.11/1.34                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 1.11/1.34               ( v2_funct_1 @ B ) ) =>
% 1.11/1.34             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 1.11/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.11/1.34    (~( ![A:$i,B:$i]:
% 1.11/1.34        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.11/1.34            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.11/1.34          ( ![C:$i]:
% 1.11/1.34            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.11/1.34                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.11/1.34              ( ( ( r2_relset_1 @
% 1.11/1.34                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 1.11/1.34                  ( v2_funct_1 @ B ) ) =>
% 1.11/1.34                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 1.11/1.34    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 1.11/1.34  thf('0', plain,
% 1.11/1.34      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf(redefinition_k6_partfun1, axiom,
% 1.11/1.34    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.11/1.34  thf('1', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 1.11/1.34      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.11/1.34  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 1.11/1.34      inference('demod', [status(thm)], ['0', '1'])).
% 1.11/1.34  thf('3', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('4', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf(redefinition_k1_partfun1, axiom,
% 1.11/1.34    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.11/1.34     ( ( ( v1_funct_1 @ E ) & 
% 1.11/1.34         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.11/1.34         ( v1_funct_1 @ F ) & 
% 1.11/1.34         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.11/1.34       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.11/1.34  thf('5', plain,
% 1.11/1.34      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.11/1.34         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.11/1.34          | ~ (v1_funct_1 @ X34)
% 1.11/1.34          | ~ (v1_funct_1 @ X37)
% 1.11/1.34          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.11/1.34          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 1.11/1.34              = (k5_relat_1 @ X34 @ X37)))),
% 1.11/1.34      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.11/1.34  thf('6', plain,
% 1.11/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.11/1.34         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 1.11/1.34            = (k5_relat_1 @ sk_C @ X0))
% 1.11/1.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.11/1.34          | ~ (v1_funct_1 @ X0)
% 1.11/1.34          | ~ (v1_funct_1 @ sk_C))),
% 1.11/1.34      inference('sup-', [status(thm)], ['4', '5'])).
% 1.11/1.34  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('8', plain,
% 1.11/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.11/1.34         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 1.11/1.34            = (k5_relat_1 @ sk_C @ X0))
% 1.11/1.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.11/1.34          | ~ (v1_funct_1 @ X0))),
% 1.11/1.34      inference('demod', [status(thm)], ['6', '7'])).
% 1.11/1.34  thf('9', plain,
% 1.11/1.34      ((~ (v1_funct_1 @ sk_B)
% 1.11/1.34        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 1.11/1.34            = (k5_relat_1 @ sk_C @ sk_B)))),
% 1.11/1.34      inference('sup-', [status(thm)], ['3', '8'])).
% 1.11/1.34  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('11', plain,
% 1.11/1.34      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.11/1.34        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('12', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('13', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf(dt_k1_partfun1, axiom,
% 1.11/1.34    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.11/1.34     ( ( ( v1_funct_1 @ E ) & 
% 1.11/1.34         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.11/1.34         ( v1_funct_1 @ F ) & 
% 1.11/1.34         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.11/1.34       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.11/1.34         ( m1_subset_1 @
% 1.11/1.34           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.11/1.34           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.11/1.34  thf('14', plain,
% 1.11/1.34      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.11/1.34         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.11/1.34          | ~ (v1_funct_1 @ X28)
% 1.11/1.34          | ~ (v1_funct_1 @ X31)
% 1.11/1.34          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.11/1.34          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 1.11/1.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 1.11/1.34      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.11/1.34  thf('15', plain,
% 1.11/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.11/1.34         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 1.11/1.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.11/1.34          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.11/1.34          | ~ (v1_funct_1 @ X1)
% 1.11/1.34          | ~ (v1_funct_1 @ sk_C))),
% 1.11/1.34      inference('sup-', [status(thm)], ['13', '14'])).
% 1.11/1.34  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('17', plain,
% 1.11/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.11/1.34         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 1.11/1.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.11/1.34          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.11/1.34          | ~ (v1_funct_1 @ X1))),
% 1.11/1.34      inference('demod', [status(thm)], ['15', '16'])).
% 1.11/1.34  thf('18', plain,
% 1.11/1.34      ((~ (v1_funct_1 @ sk_B)
% 1.11/1.34        | (m1_subset_1 @ 
% 1.11/1.34           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 1.11/1.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.11/1.34      inference('sup-', [status(thm)], ['12', '17'])).
% 1.11/1.34  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('20', plain,
% 1.11/1.34      ((m1_subset_1 @ 
% 1.11/1.34        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 1.11/1.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('demod', [status(thm)], ['18', '19'])).
% 1.11/1.34  thf(redefinition_r2_relset_1, axiom,
% 1.11/1.34    (![A:$i,B:$i,C:$i,D:$i]:
% 1.11/1.34     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.11/1.34         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.11/1.34       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.11/1.34  thf('21', plain,
% 1.11/1.34      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.11/1.34         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.11/1.34          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.11/1.34          | ((X24) = (X27))
% 1.11/1.34          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 1.11/1.34      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.11/1.34  thf('22', plain,
% 1.11/1.34      (![X0 : $i]:
% 1.11/1.34         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.11/1.34             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ X0)
% 1.11/1.34          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (X0))
% 1.11/1.34          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.11/1.34      inference('sup-', [status(thm)], ['20', '21'])).
% 1.11/1.34  thf('23', plain,
% 1.11/1.34      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.11/1.34        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B)))),
% 1.11/1.34      inference('sup-', [status(thm)], ['11', '22'])).
% 1.11/1.34  thf('24', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('25', plain,
% 1.11/1.34      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 1.11/1.34      inference('demod', [status(thm)], ['23', '24'])).
% 1.11/1.34  thf('26', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 1.11/1.34      inference('demod', [status(thm)], ['9', '10', '25'])).
% 1.11/1.34  thf('27', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf(t67_funct_2, axiom,
% 1.11/1.34    (![A:$i,B:$i]:
% 1.11/1.34     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.11/1.34         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.11/1.34       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 1.11/1.34  thf('28', plain,
% 1.11/1.34      (![X41 : $i, X42 : $i]:
% 1.11/1.34         (((k1_relset_1 @ X41 @ X41 @ X42) = (X41))
% 1.11/1.34          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))
% 1.11/1.34          | ~ (v1_funct_2 @ X42 @ X41 @ X41)
% 1.11/1.34          | ~ (v1_funct_1 @ X42))),
% 1.11/1.34      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.11/1.34  thf('29', plain,
% 1.11/1.34      ((~ (v1_funct_1 @ sk_C)
% 1.11/1.34        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 1.11/1.34        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 1.11/1.34      inference('sup-', [status(thm)], ['27', '28'])).
% 1.11/1.34  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('32', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf(redefinition_k1_relset_1, axiom,
% 1.11/1.34    (![A:$i,B:$i,C:$i]:
% 1.11/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.11/1.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.11/1.34  thf('33', plain,
% 1.11/1.34      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.11/1.34         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 1.11/1.34          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.11/1.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.11/1.34  thf('34', plain,
% 1.11/1.34      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.11/1.34      inference('sup-', [status(thm)], ['32', '33'])).
% 1.11/1.34  thf('35', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.11/1.34      inference('demod', [status(thm)], ['29', '30', '31', '34'])).
% 1.11/1.34  thf(t50_funct_1, axiom,
% 1.11/1.34    (![A:$i,B:$i]:
% 1.11/1.34     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.11/1.34       ( ![C:$i]:
% 1.11/1.34         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.11/1.34           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 1.11/1.34               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 1.11/1.34               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 1.11/1.34               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 1.11/1.34             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 1.11/1.34  thf('36', plain,
% 1.11/1.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.11/1.34         (~ (v1_relat_1 @ X9)
% 1.11/1.34          | ~ (v1_funct_1 @ X9)
% 1.11/1.34          | ((X9) = (k6_relat_1 @ X10))
% 1.11/1.34          | ((k5_relat_1 @ X9 @ X11) != (X11))
% 1.11/1.34          | ~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 1.11/1.34          | ((k1_relat_1 @ X9) != (X10))
% 1.11/1.34          | ~ (v2_funct_1 @ X11)
% 1.11/1.34          | ((k1_relat_1 @ X11) != (X10))
% 1.11/1.34          | ~ (v1_funct_1 @ X11)
% 1.11/1.34          | ~ (v1_relat_1 @ X11))),
% 1.11/1.34      inference('cnf', [status(esa)], [t50_funct_1])).
% 1.11/1.34  thf('37', plain,
% 1.11/1.34      (![X9 : $i, X11 : $i]:
% 1.11/1.34         (~ (v1_relat_1 @ X11)
% 1.11/1.34          | ~ (v1_funct_1 @ X11)
% 1.11/1.34          | ((k1_relat_1 @ X11) != (k1_relat_1 @ X9))
% 1.11/1.34          | ~ (v2_funct_1 @ X11)
% 1.11/1.34          | ~ (r1_tarski @ (k2_relat_1 @ X9) @ (k1_relat_1 @ X9))
% 1.11/1.34          | ((k5_relat_1 @ X9 @ X11) != (X11))
% 1.11/1.34          | ((X9) = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 1.11/1.34          | ~ (v1_funct_1 @ X9)
% 1.11/1.34          | ~ (v1_relat_1 @ X9))),
% 1.11/1.34      inference('simplify', [status(thm)], ['36'])).
% 1.11/1.34  thf('38', plain,
% 1.11/1.34      (![X0 : $i]:
% 1.11/1.34         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)
% 1.11/1.34          | ~ (v1_relat_1 @ sk_C)
% 1.11/1.34          | ~ (v1_funct_1 @ sk_C)
% 1.11/1.34          | ((sk_C) = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.11/1.34          | ((k5_relat_1 @ sk_C @ X0) != (X0))
% 1.11/1.34          | ~ (v2_funct_1 @ X0)
% 1.11/1.34          | ((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 1.11/1.34          | ~ (v1_funct_1 @ X0)
% 1.11/1.34          | ~ (v1_relat_1 @ X0))),
% 1.11/1.34      inference('sup-', [status(thm)], ['35', '37'])).
% 1.11/1.34  thf('39', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf(cc1_relset_1, axiom,
% 1.11/1.34    (![A:$i,B:$i,C:$i]:
% 1.11/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.11/1.34       ( v1_relat_1 @ C ) ))).
% 1.11/1.34  thf('40', plain,
% 1.11/1.34      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.11/1.34         ((v1_relat_1 @ X12)
% 1.11/1.34          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.11/1.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.11/1.34  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 1.11/1.34      inference('sup-', [status(thm)], ['39', '40'])).
% 1.11/1.34  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('43', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.11/1.34      inference('demod', [status(thm)], ['29', '30', '31', '34'])).
% 1.11/1.34  thf('44', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.11/1.34      inference('demod', [status(thm)], ['29', '30', '31', '34'])).
% 1.11/1.34  thf('45', plain,
% 1.11/1.34      (![X0 : $i]:
% 1.11/1.34         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)
% 1.11/1.34          | ((sk_C) = (k6_relat_1 @ sk_A))
% 1.11/1.34          | ((k5_relat_1 @ sk_C @ X0) != (X0))
% 1.11/1.34          | ~ (v2_funct_1 @ X0)
% 1.11/1.34          | ((k1_relat_1 @ X0) != (sk_A))
% 1.11/1.34          | ~ (v1_funct_1 @ X0)
% 1.11/1.34          | ~ (v1_relat_1 @ X0))),
% 1.11/1.34      inference('demod', [status(thm)], ['38', '41', '42', '43', '44'])).
% 1.11/1.34  thf('46', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf(dt_k2_relset_1, axiom,
% 1.11/1.34    (![A:$i,B:$i,C:$i]:
% 1.11/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.11/1.34       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.11/1.34  thf('47', plain,
% 1.11/1.34      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.11/1.34         ((m1_subset_1 @ (k2_relset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 1.11/1.34          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.11/1.34      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.11/1.34  thf('48', plain,
% 1.11/1.34      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.11/1.34      inference('sup-', [status(thm)], ['46', '47'])).
% 1.11/1.34  thf('49', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf(redefinition_k2_relset_1, axiom,
% 1.11/1.34    (![A:$i,B:$i,C:$i]:
% 1.11/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.11/1.34       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.11/1.34  thf('50', plain,
% 1.11/1.34      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.11/1.34         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 1.11/1.34          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.11/1.34      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.11/1.34  thf('51', plain,
% 1.11/1.34      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.11/1.34      inference('sup-', [status(thm)], ['49', '50'])).
% 1.11/1.34  thf('52', plain,
% 1.11/1.34      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.11/1.34      inference('demod', [status(thm)], ['48', '51'])).
% 1.11/1.34  thf(t3_subset, axiom,
% 1.11/1.34    (![A:$i,B:$i]:
% 1.11/1.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.11/1.34  thf('53', plain,
% 1.11/1.34      (![X6 : $i, X7 : $i]:
% 1.11/1.34         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.11/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.11/1.34  thf('54', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 1.11/1.34      inference('sup-', [status(thm)], ['52', '53'])).
% 1.11/1.34  thf('55', plain,
% 1.11/1.34      (![X0 : $i]:
% 1.11/1.34         (((sk_C) = (k6_relat_1 @ sk_A))
% 1.11/1.34          | ((k5_relat_1 @ sk_C @ X0) != (X0))
% 1.11/1.34          | ~ (v2_funct_1 @ X0)
% 1.11/1.34          | ((k1_relat_1 @ X0) != (sk_A))
% 1.11/1.34          | ~ (v1_funct_1 @ X0)
% 1.11/1.34          | ~ (v1_relat_1 @ X0))),
% 1.11/1.34      inference('demod', [status(thm)], ['45', '54'])).
% 1.11/1.34  thf('56', plain,
% 1.11/1.34      ((((sk_B) != (sk_B))
% 1.11/1.34        | ~ (v1_relat_1 @ sk_B)
% 1.11/1.34        | ~ (v1_funct_1 @ sk_B)
% 1.11/1.34        | ((k1_relat_1 @ sk_B) != (sk_A))
% 1.11/1.34        | ~ (v2_funct_1 @ sk_B)
% 1.11/1.34        | ((sk_C) = (k6_relat_1 @ sk_A)))),
% 1.11/1.34      inference('sup-', [status(thm)], ['26', '55'])).
% 1.11/1.34  thf('57', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('58', plain,
% 1.11/1.34      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.11/1.34         ((v1_relat_1 @ X12)
% 1.11/1.34          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.11/1.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.11/1.34  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 1.11/1.34      inference('sup-', [status(thm)], ['57', '58'])).
% 1.11/1.34  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('61', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('62', plain,
% 1.11/1.34      (![X41 : $i, X42 : $i]:
% 1.11/1.34         (((k1_relset_1 @ X41 @ X41 @ X42) = (X41))
% 1.11/1.34          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))
% 1.11/1.34          | ~ (v1_funct_2 @ X42 @ X41 @ X41)
% 1.11/1.34          | ~ (v1_funct_1 @ X42))),
% 1.11/1.34      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.11/1.34  thf('63', plain,
% 1.11/1.34      ((~ (v1_funct_1 @ sk_B)
% 1.11/1.34        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.11/1.34        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 1.11/1.34      inference('sup-', [status(thm)], ['61', '62'])).
% 1.11/1.34  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('65', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('66', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('67', plain,
% 1.11/1.34      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.11/1.34         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 1.11/1.34          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.11/1.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.11/1.34  thf('68', plain,
% 1.11/1.34      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 1.11/1.34      inference('sup-', [status(thm)], ['66', '67'])).
% 1.11/1.34  thf('69', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.11/1.34      inference('demod', [status(thm)], ['63', '64', '65', '68'])).
% 1.11/1.34  thf('70', plain, ((v2_funct_1 @ sk_B)),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('71', plain,
% 1.11/1.34      ((((sk_B) != (sk_B))
% 1.11/1.34        | ((sk_A) != (sk_A))
% 1.11/1.34        | ((sk_C) = (k6_relat_1 @ sk_A)))),
% 1.11/1.34      inference('demod', [status(thm)], ['56', '59', '60', '69', '70'])).
% 1.11/1.34  thf('72', plain, (((sk_C) = (k6_relat_1 @ sk_A))),
% 1.11/1.34      inference('simplify', [status(thm)], ['71'])).
% 1.11/1.34  thf('73', plain,
% 1.11/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.11/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.11/1.34  thf('74', plain,
% 1.11/1.34      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.11/1.34         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.11/1.34          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.11/1.34          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 1.11/1.34          | ((X24) != (X27)))),
% 1.11/1.34      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.11/1.34  thf('75', plain,
% 1.11/1.34      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.11/1.34         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 1.11/1.34          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.11/1.34      inference('simplify', [status(thm)], ['74'])).
% 1.11/1.34  thf('76', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 1.11/1.34      inference('sup-', [status(thm)], ['73', '75'])).
% 1.11/1.34  thf('77', plain, ($false),
% 1.11/1.34      inference('demod', [status(thm)], ['2', '72', '76'])).
% 1.11/1.34  
% 1.11/1.34  % SZS output end Refutation
% 1.11/1.34  
% 1.19/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
