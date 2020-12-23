%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JOWN4CbMbn

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:17 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 304 expanded)
%              Number of leaves         :   38 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          : 1038 (6295 expanded)
%              Number of equality atoms :   41 (  73 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_partfun1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
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
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != X23 )
      | ( v2_funct_2 @ X24 @ X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('18',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
      | ( v2_funct_2 @ X24 @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('49',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('50',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('51',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('54',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36 ) )
      | ( v2_funct_1 @ X40 )
      | ( X38 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X37 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('61',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('62',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62','63','64','65'])).

thf('67',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['66','67'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','68','70'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('73',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('74',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('75',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('76',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('78',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['32','73','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JOWN4CbMbn
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 273 iterations in 0.126s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.59  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.38/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.59  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.38/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.59  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.38/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.59  thf(t29_funct_2, conjecture,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.59       ( ![D:$i]:
% 0.38/0.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.38/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.38/0.59           ( ( r2_relset_1 @
% 0.38/0.59               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.38/0.59               ( k6_partfun1 @ A ) ) =>
% 0.38/0.59             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.59            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.59          ( ![D:$i]:
% 0.38/0.59            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.38/0.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.38/0.59              ( ( r2_relset_1 @
% 0.38/0.59                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.38/0.59                  ( k6_partfun1 @ A ) ) =>
% 0.38/0.59                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.38/0.59  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.38/0.59      inference('split', [status(esa)], ['0'])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.59        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.59        (k6_partfun1 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t24_funct_2, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.59       ( ![D:$i]:
% 0.38/0.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.38/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.38/0.59           ( ( r2_relset_1 @
% 0.38/0.59               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.38/0.59               ( k6_partfun1 @ B ) ) =>
% 0.38/0.59             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X32)
% 0.38/0.59          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.38/0.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.38/0.59          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 0.38/0.59               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 0.38/0.59               (k6_partfun1 @ X33))
% 0.38/0.59          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 0.38/0.59          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.38/0.59          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.38/0.59          | ~ (v1_funct_1 @ X35))),
% 0.38/0.59      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.38/0.59          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.38/0.59          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.59               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.38/0.59               (k6_partfun1 @ sk_A))
% 0.38/0.59          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.38/0.59          | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.38/0.59          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.38/0.59          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.59               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.38/0.59               (k6_partfun1 @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.38/0.59        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.38/0.59        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_D))),
% 0.38/0.59      inference('sup-', [status(thm)], ['2', '8'])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.59         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.38/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.38/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('16', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 0.38/0.59  thf(d3_funct_2, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.38/0.59       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X23 : $i, X24 : $i]:
% 0.38/0.59         (((k2_relat_1 @ X24) != (X23))
% 0.38/0.59          | (v2_funct_2 @ X24 @ X23)
% 0.38/0.59          | ~ (v5_relat_1 @ X24 @ X23)
% 0.38/0.59          | ~ (v1_relat_1 @ X24))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X24 : $i]:
% 0.38/0.59         (~ (v1_relat_1 @ X24)
% 0.38/0.59          | ~ (v5_relat_1 @ X24 @ (k2_relat_1 @ X24))
% 0.38/0.59          | (v2_funct_2 @ X24 @ (k2_relat_1 @ X24)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.38/0.59        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_D))),
% 0.38/0.59      inference('sup-', [status(thm)], ['16', '18'])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(cc2_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.59         ((v5_relat_1 @ X12 @ X14)
% 0.38/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.60  thf('22', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.38/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.60  thf('23', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc1_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( v1_relat_1 @ C ) ))).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.60         ((v1_relat_1 @ X9)
% 0.38/0.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.60  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('27', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.38/0.60      inference('demod', [status(thm)], ['19', '22', '23', '26'])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.38/0.60      inference('split', [status(esa)], ['0'])).
% 0.38/0.60  thf('29', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.60  thf('30', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.38/0.60      inference('split', [status(esa)], ['0'])).
% 0.38/0.60  thf('31', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.38/0.60      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.38/0.60  thf('32', plain, (~ (v2_funct_1 @ sk_C)),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t3_subset, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      (![X4 : $i, X5 : $i]:
% 0.38/0.60         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.60  thf('35', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.60        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.60        (k6_partfun1 @ sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(dt_k1_partfun1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.60     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.60         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.60         ( v1_funct_1 @ F ) & 
% 0.38/0.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.38/0.60       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.38/0.60         ( m1_subset_1 @
% 0.38/0.60           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.60           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.38/0.60          | ~ (v1_funct_1 @ X25)
% 0.38/0.60          | ~ (v1_funct_1 @ X28)
% 0.38/0.60          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.38/0.60          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.38/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.60  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.38/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.38/0.60          | ~ (v1_funct_1 @ X1))),
% 0.38/0.60      inference('demod', [status(thm)], ['40', '41'])).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ sk_D)
% 0.38/0.60        | (m1_subset_1 @ 
% 0.38/0.60           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['37', '42'])).
% 0.38/0.60  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      ((m1_subset_1 @ 
% 0.38/0.60        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.60  thf(redefinition_r2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.38/0.60  thf('46', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.38/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.38/0.60          | ((X18) = (X21))
% 0.38/0.60          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.38/0.60  thf('47', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.60             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.38/0.60          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.60  thf('48', plain,
% 0.38/0.60      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.38/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.38/0.60        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.38/0.60            = (k6_partfun1 @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['36', '47'])).
% 0.38/0.60  thf(t29_relset_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( m1_subset_1 @
% 0.38/0.60       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.38/0.60  thf('49', plain,
% 0.38/0.60      (![X22 : $i]:
% 0.38/0.60         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.38/0.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.38/0.60  thf(redefinition_k6_partfun1, axiom,
% 0.38/0.60    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.38/0.60  thf('50', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.60  thf('51', plain,
% 0.38/0.60      (![X22 : $i]:
% 0.38/0.60         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 0.38/0.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.38/0.60      inference('demod', [status(thm)], ['49', '50'])).
% 0.38/0.60  thf('52', plain,
% 0.38/0.60      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.38/0.60         = (k6_partfun1 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['48', '51'])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(t26_funct_2, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60       ( ![E:$i]:
% 0.38/0.60         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.38/0.60             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.38/0.60           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.38/0.60             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.38/0.60               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.38/0.60  thf('54', plain,
% 0.38/0.60      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.38/0.60         (~ (v1_funct_1 @ X36)
% 0.38/0.60          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.38/0.60          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.38/0.60          | ~ (v2_funct_1 @ (k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36))
% 0.38/0.60          | (v2_funct_1 @ X40)
% 0.38/0.60          | ((X38) = (k1_xboole_0))
% 0.38/0.60          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.38/0.60          | ~ (v1_funct_2 @ X40 @ X39 @ X37)
% 0.38/0.60          | ~ (v1_funct_1 @ X40))),
% 0.38/0.60      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.38/0.60  thf('55', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.38/0.60          | ((sk_A) = (k1_xboole_0))
% 0.38/0.60          | (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.38/0.60          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.38/0.60          | ~ (v1_funct_1 @ sk_D))),
% 0.38/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.60  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('58', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.38/0.60          | ((sk_A) = (k1_xboole_0))
% 0.38/0.60          | (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.38/0.60      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.38/0.60  thf('59', plain,
% 0.38/0.60      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.38/0.60        | (v2_funct_1 @ sk_C)
% 0.38/0.60        | ((sk_A) = (k1_xboole_0))
% 0.38/0.60        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.38/0.60        | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['52', '58'])).
% 0.38/0.60  thf(fc4_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.60       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.60  thf('60', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.38/0.60  thf('61', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.60  thf('62', plain, (![X8 : $i]: (v2_funct_1 @ (k6_partfun1 @ X8))),
% 0.38/0.60      inference('demod', [status(thm)], ['60', '61'])).
% 0.38/0.60  thf('63', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('64', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('66', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['59', '62', '63', '64', '65'])).
% 0.38/0.60  thf('67', plain, (~ (v2_funct_1 @ sk_C)),
% 0.38/0.60      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.38/0.60  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.60      inference('clc', [status(thm)], ['66', '67'])).
% 0.38/0.60  thf(t113_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.60  thf('69', plain,
% 0.38/0.60      (![X2 : $i, X3 : $i]:
% 0.38/0.60         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.60  thf('70', plain,
% 0.38/0.60      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['69'])).
% 0.38/0.60  thf('71', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.38/0.60      inference('demod', [status(thm)], ['35', '68', '70'])).
% 0.38/0.60  thf(t3_xboole_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.60  thf('72', plain,
% 0.38/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.38/0.60  thf('73', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.60  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.38/0.60  thf('74', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.38/0.60  thf('75', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.60  thf('76', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.60      inference('demod', [status(thm)], ['74', '75'])).
% 0.38/0.60  thf('77', plain, (![X8 : $i]: (v2_funct_1 @ (k6_partfun1 @ X8))),
% 0.38/0.60      inference('demod', [status(thm)], ['60', '61'])).
% 0.38/0.60  thf('78', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.38/0.60      inference('sup+', [status(thm)], ['76', '77'])).
% 0.38/0.60  thf('79', plain, ($false),
% 0.38/0.60      inference('demod', [status(thm)], ['32', '73', '78'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
