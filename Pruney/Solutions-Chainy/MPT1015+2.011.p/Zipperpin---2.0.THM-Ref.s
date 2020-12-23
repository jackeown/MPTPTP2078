%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.owu4mfpWZ7

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:48 EST 2020

% Result     : Theorem 6.37s
% Output     : Refutation 6.37s
% Verified   : 
% Statistics : Number of formulae       :  258 (22104 expanded)
%              Number of leaves         :   47 (6791 expanded)
%              Depth                    :   23
%              Number of atoms          : 2689 (474035 expanded)
%              Number of equality atoms :  107 (6161 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X65: $i,X66: $i] :
      ( ( ( k1_relset_1 @ X65 @ X65 @ X66 )
        = X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X65 ) ) )
      | ~ ( v1_funct_2 @ X66 @ X65 @ X65 )
      | ~ ( v1_funct_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X64: $i] :
      ( ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X64 ) @ ( k2_relat_1 @ X64 ) ) ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( v2_funct_1 @ X61 )
      | ( ( k2_relset_1 @ X63 @ X62 @ X61 )
       != X62 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X61 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X62 ) ) )
      | ~ ( v1_funct_2 @ X61 @ X63 @ X62 )
      | ~ ( v1_funct_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('23',plain,(
    ! [X64: $i] :
      ( ( v1_funct_2 @ X64 @ ( k1_relat_1 @ X64 ) @ ( k2_relat_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('24',plain,
    ( ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','27','30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('41',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( v2_funct_1 @ X61 )
      | ( ( k2_relset_1 @ X63 @ X62 @ X61 )
       != X62 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X62 ) ) )
      | ~ ( v1_funct_2 @ X61 @ X63 @ X62 )
      | ~ ( v1_funct_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('46',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 )
        = ( k5_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('60',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('61',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('62',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['59','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('69',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('72',plain,(
    r1_tarski @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('76',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('81',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('82',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 )
      | ( X33 != X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('83',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_relset_1 @ X34 @ X35 @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('86',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','84','85','86','87'])).

thf('89',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','88'])).

thf('90',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('93',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 )
        = ( k5_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf('100',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( r2_relset_1 @ X52 @ X53 @ ( k4_relset_1 @ X52 @ X52 @ X52 @ X53 @ ( k6_partfun1 @ X52 ) @ X54 ) @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_funct_2])).

thf('101',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('102',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( r2_relset_1 @ X52 @ X53 @ ( k4_relset_1 @ X52 @ X52 @ X52 @ X53 @ ( k6_relat_1 @ X52 ) @ X54 ) @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('106',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k4_relset_1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 )
        = ( k5_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['103','108'])).

thf('110',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','89'])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('113',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','117'])).

thf('119',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('120',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['109','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['98','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 )
        = ( k5_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('138',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('149',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['138','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['135','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ( ( v2_funct_1 @ C )
            <=> ! [D: $i,E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ D @ A )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) )
                 => ! [F: $i] :
                      ( ( ( v1_funct_1 @ F )
                        & ( v1_funct_2 @ F @ D @ A )
                        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) )
                     => ( ( r2_relset_1 @ D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) )
                       => ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) )).

thf('157',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( X55 = k1_xboole_0 )
      | ( X56 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X56 @ X55 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X55 ) ) )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X56 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X56 ) ) )
      | ~ ( r2_relset_1 @ X59 @ X55 @ ( k1_partfun1 @ X59 @ X56 @ X56 @ X55 @ X58 @ X57 ) @ ( k1_partfun1 @ X59 @ X56 @ X56 @ X55 @ X60 @ X57 ) )
      | ( r2_relset_1 @ X59 @ X56 @ X58 @ X60 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X56 ) ) )
      | ~ ( v1_funct_2 @ X60 @ X59 @ X56 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v2_funct_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_2])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['158','159','160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['155','163'])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_relset_1 @ X34 @ X35 @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('172',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('174',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','89'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('175',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('176',plain,(
    ! [X64: $i] :
      ( ( v1_funct_2 @ X64 @ ( k1_relat_1 @ X64 ) @ ( k2_relat_1 @ X64 ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X14: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('179',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,(
    v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['174','180'])).

thf('182',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','89'])).

thf('183',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['169','172','173','181','182'])).

thf('184',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('185',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['183','184'])).

thf('187',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['183','184'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('188',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('189',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','185','186','187','188'])).

thf('190',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('192',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('193',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('194',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['183','184'])).

thf('196',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['183','184'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('197',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('198',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['197'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('199',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('200',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('201',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['183','184'])).

thf('203',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['183','184'])).

thf('204',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['197'])).

thf('205',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['194','195','196','198','201','202','203','204'])).

thf('206',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('207',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_relset_1 @ X34 @ X35 @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    $false ),
    inference(demod,[status(thm)],['189','205','208'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.owu4mfpWZ7
% 0.12/0.35  % Computer   : n004.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 15:46:54 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 6.37/6.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.37/6.56  % Solved by: fo/fo7.sh
% 6.37/6.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.37/6.56  % done 10815 iterations in 6.098s
% 6.37/6.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.37/6.56  % SZS output start Refutation
% 6.37/6.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.37/6.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.37/6.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.37/6.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.37/6.56  thf(sk_B_type, type, sk_B: $i).
% 6.37/6.56  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 6.37/6.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.37/6.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.37/6.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.37/6.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.37/6.56  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.37/6.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.37/6.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.37/6.56  thf(sk_C_type, type, sk_C: $i).
% 6.37/6.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.37/6.56  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.37/6.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.37/6.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.37/6.56  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 6.37/6.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.37/6.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.37/6.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.37/6.56  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.37/6.56  thf(sk_A_type, type, sk_A: $i).
% 6.37/6.56  thf(t76_funct_2, conjecture,
% 6.37/6.56    (![A:$i,B:$i]:
% 6.37/6.56     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.37/6.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.37/6.56       ( ![C:$i]:
% 6.37/6.56         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 6.37/6.56             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.37/6.56           ( ( ( r2_relset_1 @
% 6.37/6.56                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 6.37/6.56               ( v2_funct_1 @ B ) ) =>
% 6.37/6.56             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 6.37/6.56  thf(zf_stmt_0, negated_conjecture,
% 6.37/6.56    (~( ![A:$i,B:$i]:
% 6.37/6.56        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.37/6.56            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.37/6.56          ( ![C:$i]:
% 6.37/6.56            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 6.37/6.56                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.37/6.56              ( ( ( r2_relset_1 @
% 6.37/6.56                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 6.37/6.56                  ( v2_funct_1 @ B ) ) =>
% 6.37/6.56                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 6.37/6.56    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 6.37/6.56  thf('0', plain,
% 6.37/6.56      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf(redefinition_k6_partfun1, axiom,
% 6.37/6.56    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 6.37/6.56  thf('1', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.37/6.56  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['0', '1'])).
% 6.37/6.56  thf('3', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf(t67_funct_2, axiom,
% 6.37/6.56    (![A:$i,B:$i]:
% 6.37/6.56     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.37/6.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.37/6.56       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 6.37/6.56  thf('4', plain,
% 6.37/6.56      (![X65 : $i, X66 : $i]:
% 6.37/6.56         (((k1_relset_1 @ X65 @ X65 @ X66) = (X65))
% 6.37/6.56          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X65)))
% 6.37/6.56          | ~ (v1_funct_2 @ X66 @ X65 @ X65)
% 6.37/6.56          | ~ (v1_funct_1 @ X66))),
% 6.37/6.56      inference('cnf', [status(esa)], [t67_funct_2])).
% 6.37/6.56  thf('5', plain,
% 6.37/6.56      ((~ (v1_funct_1 @ sk_B)
% 6.37/6.56        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.37/6.56        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['3', '4'])).
% 6.37/6.56  thf('6', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('7', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('8', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf(redefinition_k1_relset_1, axiom,
% 6.37/6.56    (![A:$i,B:$i,C:$i]:
% 6.37/6.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.37/6.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.37/6.56  thf('9', plain,
% 6.37/6.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.37/6.56         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 6.37/6.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.37/6.56  thf('10', plain,
% 6.37/6.56      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 6.37/6.56      inference('sup-', [status(thm)], ['8', '9'])).
% 6.37/6.56  thf('11', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 6.37/6.56  thf(t3_funct_2, axiom,
% 6.37/6.56    (![A:$i]:
% 6.37/6.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.37/6.56       ( ( v1_funct_1 @ A ) & 
% 6.37/6.56         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 6.37/6.56         ( m1_subset_1 @
% 6.37/6.56           A @ 
% 6.37/6.56           ( k1_zfmisc_1 @
% 6.37/6.56             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 6.37/6.56  thf('12', plain,
% 6.37/6.56      (![X64 : $i]:
% 6.37/6.56         ((m1_subset_1 @ X64 @ 
% 6.37/6.56           (k1_zfmisc_1 @ 
% 6.37/6.56            (k2_zfmisc_1 @ (k1_relat_1 @ X64) @ (k2_relat_1 @ X64))))
% 6.37/6.56          | ~ (v1_funct_1 @ X64)
% 6.37/6.56          | ~ (v1_relat_1 @ X64))),
% 6.37/6.56      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.37/6.56  thf('13', plain,
% 6.37/6.56      (((m1_subset_1 @ sk_B @ 
% 6.37/6.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 6.37/6.56        | ~ (v1_relat_1 @ sk_B)
% 6.37/6.56        | ~ (v1_funct_1 @ sk_B))),
% 6.37/6.56      inference('sup+', [status(thm)], ['11', '12'])).
% 6.37/6.56  thf('14', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf(cc1_relset_1, axiom,
% 6.37/6.56    (![A:$i,B:$i,C:$i]:
% 6.37/6.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.37/6.56       ( v1_relat_1 @ C ) ))).
% 6.37/6.56  thf('15', plain,
% 6.37/6.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.37/6.56         ((v1_relat_1 @ X18)
% 6.37/6.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 6.37/6.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.37/6.56  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 6.37/6.56      inference('sup-', [status(thm)], ['14', '15'])).
% 6.37/6.56  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('18', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ 
% 6.37/6.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 6.37/6.56      inference('demod', [status(thm)], ['13', '16', '17'])).
% 6.37/6.56  thf(t31_funct_2, axiom,
% 6.37/6.56    (![A:$i,B:$i,C:$i]:
% 6.37/6.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.37/6.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.37/6.56       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.37/6.56         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.37/6.56           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.37/6.56           ( m1_subset_1 @
% 6.37/6.56             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 6.37/6.56  thf('19', plain,
% 6.37/6.56      (![X61 : $i, X62 : $i, X63 : $i]:
% 6.37/6.56         (~ (v2_funct_1 @ X61)
% 6.37/6.56          | ((k2_relset_1 @ X63 @ X62 @ X61) != (X62))
% 6.37/6.56          | (m1_subset_1 @ (k2_funct_1 @ X61) @ 
% 6.37/6.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 6.37/6.56          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X62)))
% 6.37/6.56          | ~ (v1_funct_2 @ X61 @ X63 @ X62)
% 6.37/6.56          | ~ (v1_funct_1 @ X61))),
% 6.37/6.56      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.37/6.56  thf('20', plain,
% 6.37/6.56      ((~ (v1_funct_1 @ sk_B)
% 6.37/6.56        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 6.37/6.56        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 6.37/6.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 6.37/6.56        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 6.37/6.56            != (k2_relat_1 @ sk_B))
% 6.37/6.56        | ~ (v2_funct_1 @ sk_B))),
% 6.37/6.56      inference('sup-', [status(thm)], ['18', '19'])).
% 6.37/6.56  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('22', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 6.37/6.56  thf('23', plain,
% 6.37/6.56      (![X64 : $i]:
% 6.37/6.56         ((v1_funct_2 @ X64 @ (k1_relat_1 @ X64) @ (k2_relat_1 @ X64))
% 6.37/6.56          | ~ (v1_funct_1 @ X64)
% 6.37/6.56          | ~ (v1_relat_1 @ X64))),
% 6.37/6.56      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.37/6.56  thf('24', plain,
% 6.37/6.56      (((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 6.37/6.56        | ~ (v1_relat_1 @ sk_B)
% 6.37/6.56        | ~ (v1_funct_1 @ sk_B))),
% 6.37/6.56      inference('sup+', [status(thm)], ['22', '23'])).
% 6.37/6.56  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 6.37/6.56      inference('sup-', [status(thm)], ['14', '15'])).
% 6.37/6.56  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 6.37/6.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 6.37/6.56  thf('28', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ 
% 6.37/6.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 6.37/6.56      inference('demod', [status(thm)], ['13', '16', '17'])).
% 6.37/6.56  thf(redefinition_k2_relset_1, axiom,
% 6.37/6.56    (![A:$i,B:$i,C:$i]:
% 6.37/6.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.37/6.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.37/6.56  thf('29', plain,
% 6.37/6.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.37/6.56         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 6.37/6.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.37/6.56  thf('30', plain,
% 6.37/6.56      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 6.37/6.56      inference('sup-', [status(thm)], ['28', '29'])).
% 6.37/6.56  thf('31', plain, ((v2_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('32', plain,
% 6.37/6.56      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 6.37/6.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 6.37/6.56        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 6.37/6.56      inference('demod', [status(thm)], ['20', '21', '27', '30', '31'])).
% 6.37/6.56  thf('33', plain,
% 6.37/6.56      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 6.37/6.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.37/6.56      inference('simplify', [status(thm)], ['32'])).
% 6.37/6.56  thf('34', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf(dt_k1_partfun1, axiom,
% 6.37/6.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.37/6.56     ( ( ( v1_funct_1 @ E ) & 
% 6.37/6.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.37/6.56         ( v1_funct_1 @ F ) & 
% 6.37/6.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.37/6.56       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 6.37/6.56         ( m1_subset_1 @
% 6.37/6.56           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 6.37/6.56           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 6.37/6.56  thf('35', plain,
% 6.37/6.56      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 6.37/6.56          | ~ (v1_funct_1 @ X37)
% 6.37/6.56          | ~ (v1_funct_1 @ X40)
% 6.37/6.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 6.37/6.56          | (v1_funct_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)))),
% 6.37/6.56      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 6.37/6.56  thf('36', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.37/6.56          | ~ (v1_funct_1 @ X0)
% 6.37/6.56          | ~ (v1_funct_1 @ sk_B))),
% 6.37/6.56      inference('sup-', [status(thm)], ['34', '35'])).
% 6.37/6.56  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('38', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.37/6.56          | ~ (v1_funct_1 @ X0))),
% 6.37/6.56      inference('demod', [status(thm)], ['36', '37'])).
% 6.37/6.56  thf('39', plain,
% 6.37/6.56      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.37/6.56        | (v1_funct_1 @ 
% 6.37/6.56           (k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 6.37/6.56            (k2_funct_1 @ sk_B))))),
% 6.37/6.56      inference('sup-', [status(thm)], ['33', '38'])).
% 6.37/6.56  thf('40', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ 
% 6.37/6.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 6.37/6.56      inference('demod', [status(thm)], ['13', '16', '17'])).
% 6.37/6.56  thf('41', plain,
% 6.37/6.56      (![X61 : $i, X62 : $i, X63 : $i]:
% 6.37/6.56         (~ (v2_funct_1 @ X61)
% 6.37/6.56          | ((k2_relset_1 @ X63 @ X62 @ X61) != (X62))
% 6.37/6.56          | (v1_funct_1 @ (k2_funct_1 @ X61))
% 6.37/6.56          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X62)))
% 6.37/6.56          | ~ (v1_funct_2 @ X61 @ X63 @ X62)
% 6.37/6.56          | ~ (v1_funct_1 @ X61))),
% 6.37/6.56      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.37/6.56  thf('42', plain,
% 6.37/6.56      ((~ (v1_funct_1 @ sk_B)
% 6.37/6.56        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 6.37/6.56        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.37/6.56        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 6.37/6.56            != (k2_relat_1 @ sk_B))
% 6.37/6.56        | ~ (v2_funct_1 @ sk_B))),
% 6.37/6.56      inference('sup-', [status(thm)], ['40', '41'])).
% 6.37/6.56  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('44', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 6.37/6.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 6.37/6.56  thf('45', plain,
% 6.37/6.56      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 6.37/6.56      inference('sup-', [status(thm)], ['28', '29'])).
% 6.37/6.56  thf('46', plain, ((v2_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('47', plain,
% 6.37/6.56      (((v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.37/6.56        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 6.37/6.56      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 6.37/6.56  thf('48', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 6.37/6.56      inference('simplify', [status(thm)], ['47'])).
% 6.37/6.56  thf('49', plain,
% 6.37/6.56      ((v1_funct_1 @ 
% 6.37/6.56        (k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 6.37/6.56         (k2_funct_1 @ sk_B)))),
% 6.37/6.56      inference('demod', [status(thm)], ['39', '48'])).
% 6.37/6.56  thf('50', plain,
% 6.37/6.56      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 6.37/6.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.37/6.56      inference('simplify', [status(thm)], ['32'])).
% 6.37/6.56  thf('51', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf(redefinition_k1_partfun1, axiom,
% 6.37/6.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.37/6.56     ( ( ( v1_funct_1 @ E ) & 
% 6.37/6.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.37/6.56         ( v1_funct_1 @ F ) & 
% 6.37/6.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.37/6.56       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.37/6.56  thf('52', plain,
% 6.37/6.56      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 6.37/6.56          | ~ (v1_funct_1 @ X45)
% 6.37/6.56          | ~ (v1_funct_1 @ X48)
% 6.37/6.56          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 6.37/6.56          | ((k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48)
% 6.37/6.56              = (k5_relat_1 @ X45 @ X48)))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.37/6.56  thf('53', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 6.37/6.56            = (k5_relat_1 @ sk_B @ X0))
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.37/6.56          | ~ (v1_funct_1 @ X0)
% 6.37/6.56          | ~ (v1_funct_1 @ sk_B))),
% 6.37/6.56      inference('sup-', [status(thm)], ['51', '52'])).
% 6.37/6.56  thf('54', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('55', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 6.37/6.56            = (k5_relat_1 @ sk_B @ X0))
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.37/6.56          | ~ (v1_funct_1 @ X0))),
% 6.37/6.56      inference('demod', [status(thm)], ['53', '54'])).
% 6.37/6.56  thf('56', plain,
% 6.37/6.56      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.37/6.56        | ((k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 6.37/6.56            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 6.37/6.56      inference('sup-', [status(thm)], ['50', '55'])).
% 6.37/6.56  thf('57', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 6.37/6.56      inference('simplify', [status(thm)], ['47'])).
% 6.37/6.56  thf(t61_funct_1, axiom,
% 6.37/6.56    (![A:$i]:
% 6.37/6.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.37/6.56       ( ( v2_funct_1 @ A ) =>
% 6.37/6.56         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 6.37/6.56             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 6.37/6.56           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 6.37/6.56             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 6.37/6.56  thf('58', plain,
% 6.37/6.56      (![X17 : $i]:
% 6.37/6.56         (~ (v2_funct_1 @ X17)
% 6.37/6.56          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 6.37/6.56              = (k6_relat_1 @ (k1_relat_1 @ X17)))
% 6.37/6.56          | ~ (v1_funct_1 @ X17)
% 6.37/6.56          | ~ (v1_relat_1 @ X17))),
% 6.37/6.56      inference('cnf', [status(esa)], [t61_funct_1])).
% 6.37/6.56  thf('59', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 6.37/6.56  thf('60', plain,
% 6.37/6.56      (![X17 : $i]:
% 6.37/6.56         (~ (v2_funct_1 @ X17)
% 6.37/6.56          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 6.37/6.56              = (k6_relat_1 @ (k1_relat_1 @ X17)))
% 6.37/6.56          | ~ (v1_funct_1 @ X17)
% 6.37/6.56          | ~ (v1_relat_1 @ X17))),
% 6.37/6.56      inference('cnf', [status(esa)], [t61_funct_1])).
% 6.37/6.56  thf(dt_k6_partfun1, axiom,
% 6.37/6.56    (![A:$i]:
% 6.37/6.56     ( ( m1_subset_1 @
% 6.37/6.56         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 6.37/6.56       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 6.37/6.56  thf('61', plain,
% 6.37/6.56      (![X44 : $i]:
% 6.37/6.56         (m1_subset_1 @ (k6_partfun1 @ X44) @ 
% 6.37/6.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 6.37/6.56      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 6.37/6.56  thf('62', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.37/6.56  thf('63', plain,
% 6.37/6.56      (![X44 : $i]:
% 6.37/6.56         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 6.37/6.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 6.37/6.56      inference('demod', [status(thm)], ['61', '62'])).
% 6.37/6.56  thf(t3_subset, axiom,
% 6.37/6.56    (![A:$i,B:$i]:
% 6.37/6.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.37/6.56  thf('64', plain,
% 6.37/6.56      (![X7 : $i, X8 : $i]:
% 6.37/6.56         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 6.37/6.56      inference('cnf', [status(esa)], [t3_subset])).
% 6.37/6.56  thf('65', plain,
% 6.37/6.56      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 6.37/6.56      inference('sup-', [status(thm)], ['63', '64'])).
% 6.37/6.56  thf('66', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         ((r1_tarski @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 6.37/6.56           (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))
% 6.37/6.56          | ~ (v1_relat_1 @ X0)
% 6.37/6.56          | ~ (v1_funct_1 @ X0)
% 6.37/6.56          | ~ (v2_funct_1 @ X0))),
% 6.37/6.56      inference('sup+', [status(thm)], ['60', '65'])).
% 6.37/6.56  thf('67', plain,
% 6.37/6.56      (((r1_tarski @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 6.37/6.56         (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 6.37/6.56        | ~ (v2_funct_1 @ sk_B)
% 6.37/6.56        | ~ (v1_funct_1 @ sk_B)
% 6.37/6.56        | ~ (v1_relat_1 @ sk_B))),
% 6.37/6.56      inference('sup+', [status(thm)], ['59', '66'])).
% 6.37/6.56  thf('68', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 6.37/6.56  thf('69', plain, ((v2_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('70', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('71', plain, ((v1_relat_1 @ sk_B)),
% 6.37/6.56      inference('sup-', [status(thm)], ['14', '15'])).
% 6.37/6.56  thf('72', plain,
% 6.37/6.56      ((r1_tarski @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 6.37/6.56        (k2_zfmisc_1 @ sk_A @ sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 6.37/6.56  thf('73', plain,
% 6.37/6.56      (![X7 : $i, X9 : $i]:
% 6.37/6.56         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 6.37/6.56      inference('cnf', [status(esa)], [t3_subset])).
% 6.37/6.56  thf('74', plain,
% 6.37/6.56      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 6.37/6.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['72', '73'])).
% 6.37/6.56  thf('75', plain,
% 6.37/6.56      (![X44 : $i]:
% 6.37/6.56         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 6.37/6.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 6.37/6.56      inference('demod', [status(thm)], ['61', '62'])).
% 6.37/6.56  thf(redefinition_r2_relset_1, axiom,
% 6.37/6.56    (![A:$i,B:$i,C:$i,D:$i]:
% 6.37/6.56     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.37/6.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.37/6.56       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.37/6.56  thf('76', plain,
% 6.37/6.56      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 6.37/6.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 6.37/6.56          | ((X33) = (X36))
% 6.37/6.56          | ~ (r2_relset_1 @ X34 @ X35 @ X33 @ X36))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.37/6.56  thf('77', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i]:
% 6.37/6.56         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 6.37/6.56          | ((k6_relat_1 @ X0) = (X1))
% 6.37/6.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 6.37/6.56      inference('sup-', [status(thm)], ['75', '76'])).
% 6.37/6.56  thf('78', plain,
% 6.37/6.56      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 6.37/6.56        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 6.37/6.56             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 6.37/6.56      inference('sup-', [status(thm)], ['74', '77'])).
% 6.37/6.56  thf('79', plain,
% 6.37/6.56      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 6.37/6.56           (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 6.37/6.56        | ~ (v1_relat_1 @ sk_B)
% 6.37/6.56        | ~ (v1_funct_1 @ sk_B)
% 6.37/6.56        | ~ (v2_funct_1 @ sk_B)
% 6.37/6.56        | ((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 6.37/6.56      inference('sup-', [status(thm)], ['58', '78'])).
% 6.37/6.56  thf('80', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 6.37/6.56  thf('81', plain,
% 6.37/6.56      (![X44 : $i]:
% 6.37/6.56         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 6.37/6.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 6.37/6.56      inference('demod', [status(thm)], ['61', '62'])).
% 6.37/6.56  thf('82', plain,
% 6.37/6.56      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 6.37/6.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 6.37/6.56          | (r2_relset_1 @ X34 @ X35 @ X33 @ X36)
% 6.37/6.56          | ((X33) != (X36)))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.37/6.56  thf('83', plain,
% 6.37/6.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.37/6.56         ((r2_relset_1 @ X34 @ X35 @ X36 @ X36)
% 6.37/6.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 6.37/6.56      inference('simplify', [status(thm)], ['82'])).
% 6.37/6.56  thf('84', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 6.37/6.56      inference('sup-', [status(thm)], ['81', '83'])).
% 6.37/6.56  thf('85', plain, ((v1_relat_1 @ sk_B)),
% 6.37/6.56      inference('sup-', [status(thm)], ['14', '15'])).
% 6.37/6.56  thf('86', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('87', plain, ((v2_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('88', plain,
% 6.37/6.56      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 6.37/6.56      inference('demod', [status(thm)], ['79', '80', '84', '85', '86', '87'])).
% 6.37/6.56  thf('89', plain,
% 6.37/6.56      (((k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A @ sk_B @ 
% 6.37/6.56         (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['56', '57', '88'])).
% 6.37/6.56  thf('90', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['49', '89'])).
% 6.37/6.56  thf('91', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('92', plain,
% 6.37/6.56      (![X44 : $i]:
% 6.37/6.56         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 6.37/6.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 6.37/6.56      inference('demod', [status(thm)], ['61', '62'])).
% 6.37/6.56  thf('93', plain,
% 6.37/6.56      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 6.37/6.56          | ~ (v1_funct_1 @ X45)
% 6.37/6.56          | ~ (v1_funct_1 @ X48)
% 6.37/6.56          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 6.37/6.56          | ((k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48)
% 6.37/6.56              = (k5_relat_1 @ X45 @ X48)))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.37/6.56  thf('94', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.37/6.56         (((k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 6.37/6.56            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 6.37/6.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 6.37/6.56          | ~ (v1_funct_1 @ X1)
% 6.37/6.56          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['92', '93'])).
% 6.37/6.56  thf('95', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 6.37/6.56          | ~ (v1_funct_1 @ sk_B)
% 6.37/6.56          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 6.37/6.56              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['91', '94'])).
% 6.37/6.56  thf('96', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('97', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 6.37/6.56          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 6.37/6.56              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 6.37/6.56      inference('demod', [status(thm)], ['95', '96'])).
% 6.37/6.56  thf('98', plain,
% 6.37/6.56      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 6.37/6.56         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 6.37/6.56      inference('sup-', [status(thm)], ['90', '97'])).
% 6.37/6.56  thf('99', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf(t23_funct_2, axiom,
% 6.37/6.56    (![A:$i,B:$i,C:$i]:
% 6.37/6.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.37/6.56       ( ( r2_relset_1 @
% 6.37/6.56           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 6.37/6.56           C ) & 
% 6.37/6.56         ( r2_relset_1 @
% 6.37/6.56           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 6.37/6.56           C ) ) ))).
% 6.37/6.56  thf('100', plain,
% 6.37/6.56      (![X52 : $i, X53 : $i, X54 : $i]:
% 6.37/6.56         ((r2_relset_1 @ X52 @ X53 @ 
% 6.37/6.56           (k4_relset_1 @ X52 @ X52 @ X52 @ X53 @ (k6_partfun1 @ X52) @ X54) @ 
% 6.37/6.56           X54)
% 6.37/6.56          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53))))),
% 6.37/6.56      inference('cnf', [status(esa)], [t23_funct_2])).
% 6.37/6.56  thf('101', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.37/6.56  thf('102', plain,
% 6.37/6.56      (![X52 : $i, X53 : $i, X54 : $i]:
% 6.37/6.56         ((r2_relset_1 @ X52 @ X53 @ 
% 6.37/6.56           (k4_relset_1 @ X52 @ X52 @ X52 @ X53 @ (k6_relat_1 @ X52) @ X54) @ 
% 6.37/6.56           X54)
% 6.37/6.56          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53))))),
% 6.37/6.56      inference('demod', [status(thm)], ['100', '101'])).
% 6.37/6.56  thf('103', plain,
% 6.37/6.56      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.37/6.56        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 6.37/6.56        sk_B)),
% 6.37/6.56      inference('sup-', [status(thm)], ['99', '102'])).
% 6.37/6.56  thf('104', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('105', plain,
% 6.37/6.56      (![X44 : $i]:
% 6.37/6.56         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 6.37/6.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 6.37/6.56      inference('demod', [status(thm)], ['61', '62'])).
% 6.37/6.56  thf(redefinition_k4_relset_1, axiom,
% 6.37/6.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.37/6.56     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.37/6.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.37/6.56       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.37/6.56  thf('106', plain,
% 6.37/6.56      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 6.37/6.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 6.37/6.56          | ((k4_relset_1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30)
% 6.37/6.56              = (k5_relat_1 @ X27 @ X30)))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 6.37/6.56  thf('107', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.37/6.56         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 6.37/6.56            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 6.37/6.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 6.37/6.56      inference('sup-', [status(thm)], ['105', '106'])).
% 6.37/6.56  thf('108', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 6.37/6.56           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 6.37/6.56      inference('sup-', [status(thm)], ['104', '107'])).
% 6.37/6.56  thf('109', plain,
% 6.37/6.56      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.37/6.56        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)),
% 6.37/6.56      inference('demod', [status(thm)], ['103', '108'])).
% 6.37/6.56  thf('110', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['49', '89'])).
% 6.37/6.56  thf('111', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('112', plain,
% 6.37/6.56      (![X44 : $i]:
% 6.37/6.56         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 6.37/6.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 6.37/6.56      inference('demod', [status(thm)], ['61', '62'])).
% 6.37/6.56  thf('113', plain,
% 6.37/6.56      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 6.37/6.56          | ~ (v1_funct_1 @ X37)
% 6.37/6.56          | ~ (v1_funct_1 @ X40)
% 6.37/6.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 6.37/6.56          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 6.37/6.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 6.37/6.56      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 6.37/6.56  thf('114', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.37/6.56         ((m1_subset_1 @ 
% 6.37/6.56           (k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ (k6_relat_1 @ X0) @ X2) @ 
% 6.37/6.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 6.37/6.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 6.37/6.56          | ~ (v1_funct_1 @ X2)
% 6.37/6.56          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['112', '113'])).
% 6.37/6.56  thf('115', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 6.37/6.56          | ~ (v1_funct_1 @ sk_B)
% 6.37/6.56          | (m1_subset_1 @ 
% 6.37/6.56             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 6.37/6.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 6.37/6.56      inference('sup-', [status(thm)], ['111', '114'])).
% 6.37/6.56  thf('116', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('117', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 6.37/6.56          | (m1_subset_1 @ 
% 6.37/6.56             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 6.37/6.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 6.37/6.56      inference('demod', [status(thm)], ['115', '116'])).
% 6.37/6.56  thf('118', plain,
% 6.37/6.56      ((m1_subset_1 @ 
% 6.37/6.56        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 6.37/6.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['110', '117'])).
% 6.37/6.56  thf('119', plain,
% 6.37/6.56      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 6.37/6.56         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 6.37/6.56      inference('sup-', [status(thm)], ['90', '97'])).
% 6.37/6.56  thf('120', plain,
% 6.37/6.56      ((m1_subset_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 6.37/6.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('demod', [status(thm)], ['118', '119'])).
% 6.37/6.56  thf('121', plain,
% 6.37/6.56      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 6.37/6.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 6.37/6.56          | ((X33) = (X36))
% 6.37/6.56          | ~ (r2_relset_1 @ X34 @ X35 @ X33 @ X36))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.37/6.56  thf('122', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.37/6.56             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0)
% 6.37/6.56          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (X0))
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.37/6.56      inference('sup-', [status(thm)], ['120', '121'])).
% 6.37/6.56  thf('123', plain,
% 6.37/6.56      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.37/6.56        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['109', '122'])).
% 6.37/6.56  thf('124', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('125', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))),
% 6.37/6.56      inference('demod', [status(thm)], ['123', '124'])).
% 6.37/6.56  thf('126', plain,
% 6.37/6.56      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 6.37/6.56         = (sk_B))),
% 6.37/6.56      inference('demod', [status(thm)], ['98', '125'])).
% 6.37/6.56  thf('127', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('128', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('129', plain,
% 6.37/6.56      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 6.37/6.56          | ~ (v1_funct_1 @ X45)
% 6.37/6.56          | ~ (v1_funct_1 @ X48)
% 6.37/6.56          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 6.37/6.56          | ((k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48)
% 6.37/6.56              = (k5_relat_1 @ X45 @ X48)))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.37/6.56  thf('130', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 6.37/6.56            = (k5_relat_1 @ sk_C @ X0))
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.37/6.56          | ~ (v1_funct_1 @ X0)
% 6.37/6.56          | ~ (v1_funct_1 @ sk_C))),
% 6.37/6.56      inference('sup-', [status(thm)], ['128', '129'])).
% 6.37/6.56  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('132', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 6.37/6.56            = (k5_relat_1 @ sk_C @ X0))
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.37/6.56          | ~ (v1_funct_1 @ X0))),
% 6.37/6.56      inference('demod', [status(thm)], ['130', '131'])).
% 6.37/6.56  thf('133', plain,
% 6.37/6.56      ((~ (v1_funct_1 @ sk_B)
% 6.37/6.56        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 6.37/6.56            = (k5_relat_1 @ sk_C @ sk_B)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['127', '132'])).
% 6.37/6.56  thf('134', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('135', plain,
% 6.37/6.56      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 6.37/6.56         = (k5_relat_1 @ sk_C @ sk_B))),
% 6.37/6.56      inference('demod', [status(thm)], ['133', '134'])).
% 6.37/6.56  thf('136', plain,
% 6.37/6.56      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.37/6.56        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('137', plain,
% 6.37/6.56      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 6.37/6.56         = (k5_relat_1 @ sk_C @ sk_B))),
% 6.37/6.56      inference('demod', [status(thm)], ['133', '134'])).
% 6.37/6.56  thf('138', plain,
% 6.37/6.56      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 6.37/6.56      inference('demod', [status(thm)], ['136', '137'])).
% 6.37/6.56  thf('139', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('140', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('141', plain,
% 6.37/6.56      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 6.37/6.56          | ~ (v1_funct_1 @ X37)
% 6.37/6.56          | ~ (v1_funct_1 @ X40)
% 6.37/6.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 6.37/6.56          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 6.37/6.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 6.37/6.56      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 6.37/6.56  thf('142', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 6.37/6.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.37/6.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.37/6.56          | ~ (v1_funct_1 @ X1)
% 6.37/6.56          | ~ (v1_funct_1 @ sk_C))),
% 6.37/6.56      inference('sup-', [status(thm)], ['140', '141'])).
% 6.37/6.56  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('144', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 6.37/6.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.37/6.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.37/6.56          | ~ (v1_funct_1 @ X1))),
% 6.37/6.56      inference('demod', [status(thm)], ['142', '143'])).
% 6.37/6.56  thf('145', plain,
% 6.37/6.56      ((~ (v1_funct_1 @ sk_B)
% 6.37/6.56        | (m1_subset_1 @ 
% 6.37/6.56           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 6.37/6.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.37/6.56      inference('sup-', [status(thm)], ['139', '144'])).
% 6.37/6.56  thf('146', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('147', plain,
% 6.37/6.56      ((m1_subset_1 @ 
% 6.37/6.56        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 6.37/6.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('demod', [status(thm)], ['145', '146'])).
% 6.37/6.56  thf('148', plain,
% 6.37/6.56      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 6.37/6.56         = (k5_relat_1 @ sk_C @ sk_B))),
% 6.37/6.56      inference('demod', [status(thm)], ['133', '134'])).
% 6.37/6.56  thf('149', plain,
% 6.37/6.56      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 6.37/6.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('demod', [status(thm)], ['147', '148'])).
% 6.37/6.56  thf('150', plain,
% 6.37/6.56      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 6.37/6.56         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 6.37/6.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 6.37/6.56          | ((X33) = (X36))
% 6.37/6.56          | ~ (r2_relset_1 @ X34 @ X35 @ X33 @ X36))),
% 6.37/6.56      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.37/6.56  thf('151', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 6.37/6.56          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.37/6.56      inference('sup-', [status(thm)], ['149', '150'])).
% 6.37/6.56  thf('152', plain,
% 6.37/6.56      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.37/6.56        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['138', '151'])).
% 6.37/6.56  thf('153', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('154', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 6.37/6.56      inference('demod', [status(thm)], ['152', '153'])).
% 6.37/6.56  thf('155', plain,
% 6.37/6.56      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 6.37/6.56      inference('demod', [status(thm)], ['135', '154'])).
% 6.37/6.56  thf('156', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf(t27_funct_2, axiom,
% 6.37/6.56    (![A:$i,B:$i,C:$i]:
% 6.37/6.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.37/6.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.37/6.56       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 6.37/6.56            ( ~( ( v2_funct_1 @ C ) <=>
% 6.37/6.56                 ( ![D:$i,E:$i]:
% 6.37/6.56                   ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ A ) & 
% 6.37/6.56                       ( m1_subset_1 @
% 6.37/6.56                         E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 6.37/6.56                     ( ![F:$i]:
% 6.37/6.56                       ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ A ) & 
% 6.37/6.56                           ( m1_subset_1 @
% 6.37/6.56                             F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 6.37/6.56                         ( ( r2_relset_1 @
% 6.37/6.56                             D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ 
% 6.37/6.56                             ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) ) =>
% 6.37/6.56                           ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) ) ) ) ))).
% 6.37/6.56  thf('157', plain,
% 6.37/6.56      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 6.37/6.56         (((X55) = (k1_xboole_0))
% 6.37/6.56          | ((X56) = (k1_xboole_0))
% 6.37/6.56          | ~ (v1_funct_1 @ X57)
% 6.37/6.56          | ~ (v1_funct_2 @ X57 @ X56 @ X55)
% 6.37/6.56          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X55)))
% 6.37/6.56          | ~ (v1_funct_1 @ X58)
% 6.37/6.56          | ~ (v1_funct_2 @ X58 @ X59 @ X56)
% 6.37/6.56          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X56)))
% 6.37/6.56          | ~ (r2_relset_1 @ X59 @ X55 @ 
% 6.37/6.56               (k1_partfun1 @ X59 @ X56 @ X56 @ X55 @ X58 @ X57) @ 
% 6.37/6.56               (k1_partfun1 @ X59 @ X56 @ X56 @ X55 @ X60 @ X57))
% 6.37/6.56          | (r2_relset_1 @ X59 @ X56 @ X58 @ X60)
% 6.37/6.56          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X56)))
% 6.37/6.56          | ~ (v1_funct_2 @ X60 @ X59 @ X56)
% 6.37/6.56          | ~ (v1_funct_1 @ X60)
% 6.37/6.56          | ~ (v2_funct_1 @ X57))),
% 6.37/6.56      inference('cnf', [status(esa)], [t27_funct_2])).
% 6.37/6.56  thf('158', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         (~ (v2_funct_1 @ sk_B)
% 6.37/6.56          | ~ (v1_funct_1 @ X0)
% 6.37/6.56          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 6.37/6.56          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 6.37/6.56          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 6.37/6.56               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 6.37/6.56               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 6.37/6.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 6.37/6.56          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 6.37/6.56          | ~ (v1_funct_1 @ X2)
% 6.37/6.56          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.37/6.56          | ~ (v1_funct_1 @ sk_B)
% 6.37/6.56          | ((sk_A) = (k1_xboole_0))
% 6.37/6.56          | ((sk_A) = (k1_xboole_0)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['156', '157'])).
% 6.37/6.56  thf('159', plain, ((v2_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('160', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('161', plain, ((v1_funct_1 @ sk_B)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('162', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         (~ (v1_funct_1 @ X0)
% 6.37/6.56          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 6.37/6.56          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 6.37/6.56          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 6.37/6.56               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 6.37/6.56               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 6.37/6.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 6.37/6.56          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 6.37/6.56          | ~ (v1_funct_1 @ X2)
% 6.37/6.56          | ((sk_A) = (k1_xboole_0))
% 6.37/6.56          | ((sk_A) = (k1_xboole_0)))),
% 6.37/6.56      inference('demod', [status(thm)], ['158', '159', '160', '161'])).
% 6.37/6.56  thf('163', plain,
% 6.37/6.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.37/6.56         (((sk_A) = (k1_xboole_0))
% 6.37/6.56          | ~ (v1_funct_1 @ X2)
% 6.37/6.56          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 6.37/6.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 6.37/6.56          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 6.37/6.56               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 6.37/6.56               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 6.37/6.56          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 6.37/6.56          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 6.37/6.56          | ~ (v1_funct_1 @ X0))),
% 6.37/6.56      inference('simplify', [status(thm)], ['162'])).
% 6.37/6.56  thf('164', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 6.37/6.56             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 6.37/6.56          | ~ (v1_funct_1 @ X0)
% 6.37/6.56          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.37/6.56          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 6.37/6.56          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.37/6.56          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 6.37/6.56          | ~ (v1_funct_1 @ sk_C)
% 6.37/6.56          | ((sk_A) = (k1_xboole_0)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['155', '163'])).
% 6.37/6.56  thf('165', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('166', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('168', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 6.37/6.56             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 6.37/6.56          | ~ (v1_funct_1 @ X0)
% 6.37/6.56          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 6.37/6.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.37/6.56          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 6.37/6.56          | ((sk_A) = (k1_xboole_0)))),
% 6.37/6.56      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 6.37/6.56  thf('169', plain,
% 6.37/6.56      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)
% 6.37/6.56        | ((sk_A) = (k1_xboole_0))
% 6.37/6.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))
% 6.37/6.56        | ~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 6.37/6.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.37/6.56        | ~ (v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)
% 6.37/6.56        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['126', '168'])).
% 6.37/6.56  thf('170', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('171', plain,
% 6.37/6.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.37/6.56         ((r2_relset_1 @ X34 @ X35 @ X36 @ X36)
% 6.37/6.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 6.37/6.56      inference('simplify', [status(thm)], ['82'])).
% 6.37/6.56  thf('172', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 6.37/6.56      inference('sup-', [status(thm)], ['170', '171'])).
% 6.37/6.56  thf('173', plain,
% 6.37/6.56      (![X44 : $i]:
% 6.37/6.56         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 6.37/6.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 6.37/6.56      inference('demod', [status(thm)], ['61', '62'])).
% 6.37/6.56  thf('174', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['49', '89'])).
% 6.37/6.56  thf(t71_relat_1, axiom,
% 6.37/6.56    (![A:$i]:
% 6.37/6.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 6.37/6.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 6.37/6.56  thf('175', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 6.37/6.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.37/6.56  thf('176', plain,
% 6.37/6.56      (![X64 : $i]:
% 6.37/6.56         ((v1_funct_2 @ X64 @ (k1_relat_1 @ X64) @ (k2_relat_1 @ X64))
% 6.37/6.56          | ~ (v1_funct_1 @ X64)
% 6.37/6.56          | ~ (v1_relat_1 @ X64))),
% 6.37/6.56      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.37/6.56  thf('177', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ 
% 6.37/6.56           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 6.37/6.56          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 6.37/6.56          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 6.37/6.56      inference('sup+', [status(thm)], ['175', '176'])).
% 6.37/6.56  thf('178', plain, (![X14 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 6.37/6.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.37/6.56  thf(fc4_funct_1, axiom,
% 6.37/6.56    (![A:$i]:
% 6.37/6.56     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 6.37/6.56       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 6.37/6.56  thf('179', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 6.37/6.56      inference('cnf', [status(esa)], [fc4_funct_1])).
% 6.37/6.56  thf('180', plain,
% 6.37/6.56      (![X0 : $i]:
% 6.37/6.56         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ X0)
% 6.37/6.56          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 6.37/6.56      inference('demod', [status(thm)], ['177', '178', '179'])).
% 6.37/6.56  thf('181', plain, ((v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)),
% 6.37/6.56      inference('sup-', [status(thm)], ['174', '180'])).
% 6.37/6.56  thf('182', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['49', '89'])).
% 6.37/6.56  thf('183', plain,
% 6.37/6.56      ((((sk_A) = (k1_xboole_0))
% 6.37/6.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A)))),
% 6.37/6.56      inference('demod', [status(thm)], ['169', '172', '173', '181', '182'])).
% 6.37/6.56  thf('184', plain,
% 6.37/6.56      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 6.37/6.56      inference('demod', [status(thm)], ['0', '1'])).
% 6.37/6.56  thf('185', plain, (((sk_A) = (k1_xboole_0))),
% 6.37/6.56      inference('clc', [status(thm)], ['183', '184'])).
% 6.37/6.56  thf('186', plain, (((sk_A) = (k1_xboole_0))),
% 6.37/6.56      inference('clc', [status(thm)], ['183', '184'])).
% 6.37/6.56  thf('187', plain, (((sk_A) = (k1_xboole_0))),
% 6.37/6.56      inference('clc', [status(thm)], ['183', '184'])).
% 6.37/6.56  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 6.37/6.56  thf('188', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.37/6.56      inference('cnf', [status(esa)], [t81_relat_1])).
% 6.37/6.56  thf('189', plain,
% 6.37/6.56      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0)),
% 6.37/6.56      inference('demod', [status(thm)], ['2', '185', '186', '187', '188'])).
% 6.37/6.56  thf('190', plain,
% 6.37/6.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.37/6.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.37/6.56  thf('191', plain,
% 6.37/6.56      (![X7 : $i, X8 : $i]:
% 6.37/6.56         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 6.37/6.56      inference('cnf', [status(esa)], [t3_subset])).
% 6.37/6.56  thf('192', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 6.37/6.56      inference('sup-', [status(thm)], ['190', '191'])).
% 6.37/6.56  thf(d10_xboole_0, axiom,
% 6.37/6.56    (![A:$i,B:$i]:
% 6.37/6.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.37/6.56  thf('193', plain,
% 6.37/6.56      (![X0 : $i, X2 : $i]:
% 6.37/6.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.37/6.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.37/6.56  thf('194', plain,
% 6.37/6.56      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_C)
% 6.37/6.56        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_C)))),
% 6.37/6.56      inference('sup-', [status(thm)], ['192', '193'])).
% 6.37/6.56  thf('195', plain, (((sk_A) = (k1_xboole_0))),
% 6.37/6.56      inference('clc', [status(thm)], ['183', '184'])).
% 6.37/6.56  thf('196', plain, (((sk_A) = (k1_xboole_0))),
% 6.37/6.56      inference('clc', [status(thm)], ['183', '184'])).
% 6.37/6.56  thf(t113_zfmisc_1, axiom,
% 6.37/6.56    (![A:$i,B:$i]:
% 6.37/6.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.37/6.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.37/6.56  thf('197', plain,
% 6.37/6.56      (![X4 : $i, X5 : $i]:
% 6.37/6.57         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 6.37/6.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.37/6.57  thf('198', plain,
% 6.37/6.57      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 6.37/6.57      inference('simplify', [status(thm)], ['197'])).
% 6.37/6.57  thf(t4_subset_1, axiom,
% 6.37/6.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.37/6.57  thf('199', plain,
% 6.37/6.57      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 6.37/6.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.37/6.57  thf('200', plain,
% 6.37/6.57      (![X7 : $i, X8 : $i]:
% 6.37/6.57         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 6.37/6.57      inference('cnf', [status(esa)], [t3_subset])).
% 6.37/6.57  thf('201', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.37/6.57      inference('sup-', [status(thm)], ['199', '200'])).
% 6.37/6.57  thf('202', plain, (((sk_A) = (k1_xboole_0))),
% 6.37/6.57      inference('clc', [status(thm)], ['183', '184'])).
% 6.37/6.57  thf('203', plain, (((sk_A) = (k1_xboole_0))),
% 6.37/6.57      inference('clc', [status(thm)], ['183', '184'])).
% 6.37/6.57  thf('204', plain,
% 6.37/6.57      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 6.37/6.57      inference('simplify', [status(thm)], ['197'])).
% 6.37/6.57  thf('205', plain, (((k1_xboole_0) = (sk_C))),
% 6.37/6.57      inference('demod', [status(thm)],
% 6.37/6.57                ['194', '195', '196', '198', '201', '202', '203', '204'])).
% 6.37/6.57  thf('206', plain,
% 6.37/6.57      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 6.37/6.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.37/6.57  thf('207', plain,
% 6.37/6.57      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.37/6.57         ((r2_relset_1 @ X34 @ X35 @ X36 @ X36)
% 6.37/6.57          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 6.37/6.57      inference('simplify', [status(thm)], ['82'])).
% 6.37/6.57  thf('208', plain,
% 6.37/6.57      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 6.37/6.57      inference('sup-', [status(thm)], ['206', '207'])).
% 6.37/6.57  thf('209', plain, ($false),
% 6.37/6.57      inference('demod', [status(thm)], ['189', '205', '208'])).
% 6.37/6.57  
% 6.37/6.57  % SZS output end Refutation
% 6.37/6.57  
% 6.40/6.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
