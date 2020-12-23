%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CKYZZHUUjw

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:13 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 339 expanded)
%              Number of leaves         :   43 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          : 1127 (6468 expanded)
%              Number of equality atoms :   34 (  68 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

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
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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

thf('4',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_partfun1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_2 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_2 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( ( k2_relset_1 @ sk_B_2 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_relat_1 @ X33 )
       != X32 )
      | ( v2_funct_2 @ X33 @ X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('18',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) )
      | ( v2_funct_2 @ X33 @ ( k2_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['19','22','23','26'])).

thf('28',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('42',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('52',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('53',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
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

thf('57',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X46 @ X46 @ X47 @ X49 @ X45 ) )
      | ( v2_funct_1 @ X49 )
      | ( X47 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X46 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_2 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_2 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_2 @ sk_D @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_2 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('64',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','65','66','67','68'])).

thf('70',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['69','70'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('72',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('73',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['38','71','76'])).

thf('78',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','77'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('79',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('80',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','75'])).

thf('82',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('84',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('85',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('93',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['32','80','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CKYZZHUUjw
% 0.15/0.34  % Computer   : n003.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:54:12 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 294 iterations in 0.177s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.44/0.63  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.44/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.63  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.44/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.44/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.44/0.63  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.63  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.44/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.63  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.44/0.63  thf(t29_funct_2, conjecture,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.63       ( ![D:$i]:
% 0.44/0.63         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.44/0.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.44/0.63           ( ( r2_relset_1 @
% 0.44/0.63               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.44/0.63               ( k6_partfun1 @ A ) ) =>
% 0.44/0.63             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.64        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.64            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.64          ( ![D:$i]:
% 0.44/0.64            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.44/0.64                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.44/0.64              ( ( r2_relset_1 @
% 0.44/0.64                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.44/0.64                  ( k6_partfun1 @ A ) ) =>
% 0.44/0.64                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.44/0.64    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.44/0.64  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('1', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 0.44/0.64      inference('split', [status(esa)], ['0'])).
% 0.44/0.64  thf('2', plain,
% 0.44/0.64      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.44/0.64        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.44/0.64        (k6_partfun1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('3', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(t24_funct_2, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.64       ( ![D:$i]:
% 0.44/0.64         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.44/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.44/0.64           ( ( r2_relset_1 @
% 0.44/0.64               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.44/0.64               ( k6_partfun1 @ B ) ) =>
% 0.44/0.64             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.44/0.64  thf('4', plain,
% 0.44/0.64      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.44/0.64         (~ (v1_funct_1 @ X41)
% 0.44/0.64          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.44/0.64          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.44/0.64          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 0.44/0.64               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 0.44/0.64               (k6_partfun1 @ X42))
% 0.44/0.64          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 0.44/0.64          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.44/0.64          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 0.44/0.64          | ~ (v1_funct_1 @ X44))),
% 0.44/0.64      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.44/0.64  thf('5', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (v1_funct_1 @ X0)
% 0.44/0.64          | ~ (v1_funct_2 @ X0 @ sk_B_2 @ sk_A)
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 0.44/0.64          | ((k2_relset_1 @ sk_B_2 @ sk_A @ X0) = (sk_A))
% 0.44/0.64          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.44/0.64               (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0) @ 
% 0.44/0.64               (k6_partfun1 @ sk_A))
% 0.44/0.64          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.44/0.64          | ~ (v1_funct_1 @ sk_C_1))),
% 0.44/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.64  thf('6', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('7', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('8', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (v1_funct_1 @ X0)
% 0.44/0.64          | ~ (v1_funct_2 @ X0 @ sk_B_2 @ sk_A)
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 0.44/0.64          | ((k2_relset_1 @ sk_B_2 @ sk_A @ X0) = (sk_A))
% 0.44/0.64          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.44/0.64               (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0) @ 
% 0.44/0.64               (k6_partfun1 @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.44/0.64  thf('9', plain,
% 0.44/0.64      ((((k2_relset_1 @ sk_B_2 @ sk_A @ sk_D) = (sk_A))
% 0.44/0.64        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 0.44/0.64        | ~ (v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)
% 0.44/0.64        | ~ (v1_funct_1 @ sk_D))),
% 0.44/0.64      inference('sup-', [status(thm)], ['2', '8'])).
% 0.44/0.64  thf('10', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.44/0.64  thf('11', plain,
% 0.44/0.64      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.64         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.44/0.64          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.44/0.64  thf('12', plain,
% 0.44/0.64      (((k2_relset_1 @ sk_B_2 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.44/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.64  thf('13', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('16', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.44/0.64      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 0.44/0.64  thf(d3_funct_2, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.44/0.64       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.44/0.64  thf('17', plain,
% 0.44/0.64      (![X32 : $i, X33 : $i]:
% 0.44/0.64         (((k2_relat_1 @ X33) != (X32))
% 0.44/0.64          | (v2_funct_2 @ X33 @ X32)
% 0.44/0.64          | ~ (v5_relat_1 @ X33 @ X32)
% 0.44/0.64          | ~ (v1_relat_1 @ X33))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.44/0.64  thf('18', plain,
% 0.44/0.64      (![X33 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X33)
% 0.44/0.64          | ~ (v5_relat_1 @ X33 @ (k2_relat_1 @ X33))
% 0.44/0.64          | (v2_funct_2 @ X33 @ (k2_relat_1 @ X33)))),
% 0.44/0.64      inference('simplify', [status(thm)], ['17'])).
% 0.44/0.64  thf('19', plain,
% 0.44/0.64      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.44/0.64        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.44/0.64        | ~ (v1_relat_1 @ sk_D))),
% 0.44/0.64      inference('sup-', [status(thm)], ['16', '18'])).
% 0.44/0.64  thf('20', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(cc2_relset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.64  thf('21', plain,
% 0.44/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.64         ((v5_relat_1 @ X21 @ X23)
% 0.44/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.44/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.64  thf('22', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.44/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.64  thf('23', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.44/0.64      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 0.44/0.64  thf('24', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(cc1_relset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.64       ( v1_relat_1 @ C ) ))).
% 0.44/0.64  thf('25', plain,
% 0.44/0.64      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.64         ((v1_relat_1 @ X18)
% 0.44/0.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.44/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.64  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.44/0.64  thf('27', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.44/0.64      inference('demod', [status(thm)], ['19', '22', '23', '26'])).
% 0.44/0.64  thf('28', plain,
% 0.44/0.64      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.44/0.64      inference('split', [status(esa)], ['0'])).
% 0.44/0.64  thf('29', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['27', '28'])).
% 0.44/0.64  thf('30', plain,
% 0.44/0.64      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.44/0.64      inference('split', [status(esa)], ['0'])).
% 0.44/0.64  thf('31', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 0.44/0.64      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.44/0.64  thf('32', plain, (~ (v2_funct_1 @ sk_C_1)),
% 0.44/0.64      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.44/0.64  thf(d1_xboole_0, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.44/0.64  thf('33', plain,
% 0.44/0.64      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.44/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.64  thf(fc4_zfmisc_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.44/0.64  thf('34', plain,
% 0.44/0.64      (![X5 : $i, X6 : $i]:
% 0.44/0.64         (~ (v1_xboole_0 @ X5) | (v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.44/0.64  thf('35', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(t5_subset, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.44/0.64          ( v1_xboole_0 @ C ) ) ))).
% 0.44/0.64  thf('36', plain,
% 0.44/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X7 @ X8)
% 0.44/0.64          | ~ (v1_xboole_0 @ X9)
% 0.44/0.64          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t5_subset])).
% 0.44/0.64  thf('37', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.44/0.64          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.44/0.64      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.64  thf('38', plain,
% 0.44/0.64      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.44/0.64      inference('sup-', [status(thm)], ['34', '37'])).
% 0.44/0.64  thf('39', plain,
% 0.44/0.64      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.44/0.64        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.44/0.64        (k6_partfun1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('40', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('41', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(dt_k1_partfun1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.64     ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.44/0.64         ( v1_funct_1 @ F ) & 
% 0.44/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.44/0.64       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.44/0.64         ( m1_subset_1 @
% 0.44/0.64           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.44/0.64  thf('42', plain,
% 0.44/0.64      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.44/0.64          | ~ (v1_funct_1 @ X34)
% 0.44/0.64          | ~ (v1_funct_1 @ X37)
% 0.44/0.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.44/0.64          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 0.44/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.44/0.64  thf('43', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((m1_subset_1 @ 
% 0.44/0.64           (k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 0.44/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.44/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.44/0.64          | ~ (v1_funct_1 @ X1)
% 0.44/0.64          | ~ (v1_funct_1 @ sk_C_1))),
% 0.44/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.44/0.64  thf('44', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('45', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((m1_subset_1 @ 
% 0.44/0.64           (k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 0.44/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.44/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.44/0.64          | ~ (v1_funct_1 @ X1))),
% 0.44/0.64      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.64  thf('46', plain,
% 0.44/0.64      ((~ (v1_funct_1 @ sk_D)
% 0.44/0.64        | (m1_subset_1 @ 
% 0.44/0.64           (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.44/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['40', '45'])).
% 0.44/0.64  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('48', plain,
% 0.44/0.64      ((m1_subset_1 @ 
% 0.44/0.64        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.44/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['46', '47'])).
% 0.44/0.64  thf(redefinition_r2_relset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.64     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.44/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.64       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.44/0.64  thf('49', plain,
% 0.44/0.64      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.44/0.64          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.44/0.64          | ((X27) = (X30))
% 0.44/0.64          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.44/0.64  thf('50', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.44/0.64             (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 0.44/0.64          | ((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D)
% 0.44/0.64              = (X0))
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['48', '49'])).
% 0.44/0.64  thf('51', plain,
% 0.44/0.64      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.44/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.44/0.64        | ((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D)
% 0.44/0.64            = (k6_partfun1 @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['39', '50'])).
% 0.44/0.64  thf(t29_relset_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( m1_subset_1 @
% 0.44/0.64       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.44/0.64  thf('52', plain,
% 0.44/0.64      (![X31 : $i]:
% 0.44/0.64         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.44/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.44/0.64  thf(redefinition_k6_partfun1, axiom,
% 0.44/0.64    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.44/0.64  thf('53', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.64  thf('54', plain,
% 0.44/0.64      (![X31 : $i]:
% 0.44/0.64         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 0.44/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.44/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.44/0.64  thf('55', plain,
% 0.44/0.64      (((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D)
% 0.44/0.64         = (k6_partfun1 @ sk_A))),
% 0.44/0.64      inference('demod', [status(thm)], ['51', '54'])).
% 0.44/0.64  thf('56', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(t26_funct_2, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.64       ( ![E:$i]:
% 0.44/0.64         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.44/0.64             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.44/0.64           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.44/0.64             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.44/0.64               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.44/0.64  thf('57', plain,
% 0.44/0.64      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.44/0.64         (~ (v1_funct_1 @ X45)
% 0.44/0.64          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 0.44/0.64          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.44/0.64          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X46 @ X46 @ X47 @ X49 @ X45))
% 0.44/0.64          | (v2_funct_1 @ X49)
% 0.44/0.64          | ((X47) = (k1_xboole_0))
% 0.44/0.64          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 0.44/0.64          | ~ (v1_funct_2 @ X49 @ X48 @ X46)
% 0.44/0.64          | ~ (v1_funct_1 @ X49))),
% 0.44/0.64      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.44/0.64  thf('58', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (v1_funct_1 @ X0)
% 0.44/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_2)
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_2)))
% 0.44/0.64          | ((sk_A) = (k1_xboole_0))
% 0.44/0.64          | (v2_funct_1 @ X0)
% 0.44/0.64          | ~ (v2_funct_1 @ 
% 0.44/0.64               (k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D))
% 0.44/0.64          | ~ (v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)
% 0.44/0.64          | ~ (v1_funct_1 @ sk_D))),
% 0.44/0.64      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.64  thf('59', plain, ((v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('61', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (v1_funct_1 @ X0)
% 0.44/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_2)
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_2)))
% 0.44/0.64          | ((sk_A) = (k1_xboole_0))
% 0.44/0.64          | (v2_funct_1 @ X0)
% 0.44/0.64          | ~ (v2_funct_1 @ 
% 0.44/0.64               (k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D)))),
% 0.44/0.64      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.44/0.64  thf('62', plain,
% 0.44/0.64      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.44/0.64        | (v2_funct_1 @ sk_C_1)
% 0.44/0.64        | ((sk_A) = (k1_xboole_0))
% 0.44/0.64        | ~ (m1_subset_1 @ sk_C_1 @ 
% 0.44/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.44/0.64        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.44/0.64        | ~ (v1_funct_1 @ sk_C_1))),
% 0.44/0.64      inference('sup-', [status(thm)], ['55', '61'])).
% 0.44/0.64  thf(fc4_funct_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.44/0.64       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.44/0.64  thf('63', plain, (![X15 : $i]: (v2_funct_1 @ (k6_relat_1 @ X15))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.44/0.64  thf('64', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.64  thf('65', plain, (![X15 : $i]: (v2_funct_1 @ (k6_partfun1 @ X15))),
% 0.44/0.64      inference('demod', [status(thm)], ['63', '64'])).
% 0.44/0.64  thf('66', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('67', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('68', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('69', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.64      inference('demod', [status(thm)], ['62', '65', '66', '67', '68'])).
% 0.44/0.64  thf('70', plain, (~ (v2_funct_1 @ sk_C_1)),
% 0.44/0.64      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.44/0.64  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 0.44/0.64      inference('clc', [status(thm)], ['69', '70'])).
% 0.44/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.64  thf('72', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.44/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.64  thf('73', plain,
% 0.44/0.64      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.44/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.64  thf(t7_ordinal1, axiom,
% 0.44/0.64    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.64  thf('74', plain,
% 0.44/0.64      (![X16 : $i, X17 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.44/0.64      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.44/0.64  thf('75', plain,
% 0.44/0.64      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['73', '74'])).
% 0.44/0.64  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.64      inference('sup-', [status(thm)], ['72', '75'])).
% 0.44/0.64  thf('77', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 0.44/0.64      inference('demod', [status(thm)], ['38', '71', '76'])).
% 0.44/0.64  thf('78', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.44/0.64      inference('sup-', [status(thm)], ['33', '77'])).
% 0.44/0.64  thf(l13_xboole_0, axiom,
% 0.44/0.64    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.64  thf('79', plain,
% 0.44/0.64      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.44/0.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.64  thf('80', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['78', '79'])).
% 0.44/0.64  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.64      inference('sup-', [status(thm)], ['72', '75'])).
% 0.44/0.64  thf('82', plain,
% 0.44/0.64      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.44/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.64  thf('83', plain,
% 0.44/0.64      (![X5 : $i, X6 : $i]:
% 0.44/0.64         (~ (v1_xboole_0 @ X5) | (v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.44/0.64  thf('84', plain,
% 0.44/0.64      (![X31 : $i]:
% 0.44/0.64         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 0.44/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.44/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.44/0.64  thf('85', plain,
% 0.44/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X7 @ X8)
% 0.44/0.64          | ~ (v1_xboole_0 @ X9)
% 0.44/0.64          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t5_subset])).
% 0.44/0.64  thf('86', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.44/0.64          | ~ (r2_hidden @ X1 @ (k6_partfun1 @ X0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['84', '85'])).
% 0.44/0.64  thf('87', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k6_partfun1 @ X0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['83', '86'])).
% 0.44/0.64  thf('88', plain,
% 0.44/0.64      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['82', '87'])).
% 0.44/0.64  thf('89', plain,
% 0.44/0.64      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.44/0.64      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.64  thf('90', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (v1_xboole_0 @ X0) | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['88', '89'])).
% 0.44/0.64  thf('91', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['81', '90'])).
% 0.44/0.64  thf('92', plain, (![X15 : $i]: (v2_funct_1 @ (k6_partfun1 @ X15))),
% 0.44/0.64      inference('demod', [status(thm)], ['63', '64'])).
% 0.44/0.64  thf('93', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.44/0.64      inference('sup+', [status(thm)], ['91', '92'])).
% 0.44/0.64  thf('94', plain, ($false),
% 0.44/0.64      inference('demod', [status(thm)], ['32', '80', '93'])).
% 0.44/0.64  
% 0.44/0.64  % SZS output end Refutation
% 0.44/0.64  
% 0.44/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
