%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RLYGEFfuQz

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:12 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 493 expanded)
%              Number of leaves         :   41 ( 162 expanded)
%              Depth                    :   17
%              Number of atoms          : 1287 (9891 expanded)
%              Number of equality atoms :   48 ( 124 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('15',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('16',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_partfun1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['25','29','32','33','34','35'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('37',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ X29 )
       != X28 )
      | ( v2_funct_2 @ X29 @ X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('38',plain,(
    ! [X29: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
      | ( v2_funct_2 @ X29 @ ( k2_relat_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['25','29','32','33','34','35'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['39','42','43','46'])).

thf('48',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('55',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('62',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('64',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('65',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('66',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('67',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','67','68','69','70','73'])).

thf('75',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('76',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('77',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('83',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['81','82'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('84',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('87',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('89',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('90',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['79','80','87','88','89','90','91'])).

thf('93',plain,
    ( ( sk_A != sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['74','92'])).

thf('94',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['93'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('95',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v2_funct_1 @ X11 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('100',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('101',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('102',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('105',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['96','97','98','99','102','103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['52','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RLYGEFfuQz
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 327 iterations in 0.187s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.40/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.61  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.40/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.61  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.40/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.61  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.40/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.61  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.40/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.61  thf(t29_funct_2, conjecture,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.61       ( ![D:$i]:
% 0.40/0.61         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.40/0.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.40/0.61           ( ( r2_relset_1 @
% 0.40/0.61               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.40/0.61               ( k6_partfun1 @ A ) ) =>
% 0.40/0.61             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.61          ( ![D:$i]:
% 0.40/0.61            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.40/0.61                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.40/0.61              ( ( r2_relset_1 @
% 0.40/0.61                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.40/0.61                  ( k6_partfun1 @ A ) ) =>
% 0.40/0.61                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.40/0.61  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.40/0.61      inference('split', [status(esa)], ['0'])).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.40/0.61        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.40/0.61        (k6_partfun1 @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(dt_k1_partfun1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.61     ( ( ( v1_funct_1 @ E ) & 
% 0.40/0.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.61         ( v1_funct_1 @ F ) & 
% 0.40/0.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.40/0.61       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.40/0.61         ( m1_subset_1 @
% 0.40/0.61           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.40/0.61           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.40/0.61          | ~ (v1_funct_1 @ X30)
% 0.40/0.61          | ~ (v1_funct_1 @ X33)
% 0.40/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.40/0.61          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 0.40/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.40/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.40/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.40/0.61          | ~ (v1_funct_1 @ X1)
% 0.40/0.61          | ~ (v1_funct_1 @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.61  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.40/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.40/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.40/0.61          | ~ (v1_funct_1 @ X1))),
% 0.40/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      ((~ (v1_funct_1 @ sk_D)
% 0.40/0.61        | (m1_subset_1 @ 
% 0.40/0.61           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.40/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['3', '8'])).
% 0.40/0.61  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      ((m1_subset_1 @ 
% 0.40/0.61        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.40/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.61  thf(redefinition_r2_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.61     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.61       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.40/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.40/0.61          | ((X23) = (X26))
% 0.40/0.61          | ~ (r2_relset_1 @ X24 @ X25 @ X23 @ X26))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.40/0.61             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.40/0.61          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.40/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.40/0.61        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.40/0.61            = (k6_partfun1 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['2', '13'])).
% 0.40/0.61  thf(t29_relset_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( m1_subset_1 @
% 0.40/0.61       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (![X27 : $i]:
% 0.40/0.61         (m1_subset_1 @ (k6_relat_1 @ X27) @ 
% 0.40/0.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.40/0.61  thf(redefinition_k6_partfun1, axiom,
% 0.40/0.61    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.40/0.61  thf('16', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (![X27 : $i]:
% 0.40/0.61         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 0.40/0.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.40/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.40/0.61         = (k6_partfun1 @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['14', '17'])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(t24_funct_2, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.61       ( ![D:$i]:
% 0.40/0.61         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.40/0.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.40/0.61           ( ( r2_relset_1 @
% 0.40/0.61               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.40/0.61               ( k6_partfun1 @ B ) ) =>
% 0.40/0.61             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.40/0.61         (~ (v1_funct_1 @ X43)
% 0.40/0.61          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.40/0.61          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.40/0.61          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 0.40/0.61               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 0.40/0.61               (k6_partfun1 @ X44))
% 0.40/0.61          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 0.40/0.61          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.40/0.61          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 0.40/0.61          | ~ (v1_funct_1 @ X46))),
% 0.40/0.61      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_funct_1 @ X0)
% 0.40/0.61          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.40/0.61          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.40/0.61          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.40/0.61               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.40/0.61               (k6_partfun1 @ sk_A))
% 0.40/0.61          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.40/0.61          | ~ (v1_funct_1 @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.61  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_funct_1 @ X0)
% 0.40/0.61          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.40/0.61          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.40/0.61          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.40/0.61               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.40/0.61               (k6_partfun1 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.40/0.61           (k6_partfun1 @ sk_A))
% 0.40/0.61        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.40/0.61        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.40/0.61        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.40/0.61        | ~ (v1_funct_1 @ sk_D))),
% 0.40/0.61      inference('sup-', [status(thm)], ['18', '24'])).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      (![X27 : $i]:
% 0.40/0.61         (m1_subset_1 @ (k6_partfun1 @ X27) @ 
% 0.40/0.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))),
% 0.40/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.40/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.40/0.61          | (r2_relset_1 @ X24 @ X25 @ X23 @ X26)
% 0.40/0.61          | ((X23) != (X26)))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.61         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 0.40/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.40/0.61      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['26', '28'])).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(redefinition_k2_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.61         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 0.40/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.40/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.61  thf('33', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('36', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['25', '29', '32', '33', '34', '35'])).
% 0.40/0.61  thf(d3_funct_2, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.40/0.61       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      (![X28 : $i, X29 : $i]:
% 0.40/0.61         (((k2_relat_1 @ X29) != (X28))
% 0.40/0.61          | (v2_funct_2 @ X29 @ X28)
% 0.40/0.61          | ~ (v5_relat_1 @ X29 @ X28)
% 0.40/0.61          | ~ (v1_relat_1 @ X29))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.40/0.61  thf('38', plain,
% 0.40/0.61      (![X29 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X29)
% 0.40/0.61          | ~ (v5_relat_1 @ X29 @ (k2_relat_1 @ X29))
% 0.40/0.61          | (v2_funct_2 @ X29 @ (k2_relat_1 @ X29)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['37'])).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.40/0.61        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_D))),
% 0.40/0.61      inference('sup-', [status(thm)], ['36', '38'])).
% 0.40/0.61  thf('40', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(cc2_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.61  thf('41', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.61         ((v5_relat_1 @ X17 @ X19)
% 0.40/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.61  thf('42', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.40/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.61  thf('43', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['25', '29', '32', '33', '34', '35'])).
% 0.40/0.61  thf('44', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(cc1_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( v1_relat_1 @ C ) ))).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.61         ((v1_relat_1 @ X14)
% 0.40/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.61  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.61  thf('47', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.40/0.61      inference('demod', [status(thm)], ['39', '42', '43', '46'])).
% 0.40/0.61  thf('48', plain,
% 0.40/0.61      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.40/0.61      inference('split', [status(esa)], ['0'])).
% 0.40/0.61  thf('49', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.61  thf('50', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.40/0.61      inference('split', [status(esa)], ['0'])).
% 0.40/0.61  thf('51', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.40/0.61  thf('52', plain, (~ (v2_funct_1 @ sk_C)),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['1', '51'])).
% 0.40/0.61  thf('53', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('54', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(redefinition_k1_partfun1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.61     ( ( ( v1_funct_1 @ E ) & 
% 0.40/0.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.61         ( v1_funct_1 @ F ) & 
% 0.40/0.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.40/0.61       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.40/0.61  thf('55', plain,
% 0.40/0.61      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.40/0.61          | ~ (v1_funct_1 @ X36)
% 0.40/0.61          | ~ (v1_funct_1 @ X39)
% 0.40/0.61          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.40/0.61          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.40/0.61              = (k5_relat_1 @ X36 @ X39)))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.40/0.61  thf('56', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.40/0.61            = (k5_relat_1 @ sk_C @ X0))
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.40/0.61          | ~ (v1_funct_1 @ X0)
% 0.40/0.61          | ~ (v1_funct_1 @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.40/0.61  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('58', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.40/0.61            = (k5_relat_1 @ sk_C @ X0))
% 0.40/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.40/0.61          | ~ (v1_funct_1 @ X0))),
% 0.40/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.40/0.61  thf('59', plain,
% 0.40/0.61      ((~ (v1_funct_1 @ sk_D)
% 0.40/0.61        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.40/0.61            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['53', '58'])).
% 0.40/0.61  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('61', plain,
% 0.40/0.61      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.40/0.61         = (k6_partfun1 @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['14', '17'])).
% 0.40/0.61  thf('62', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.40/0.61      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.40/0.61  thf(t27_funct_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.61           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.40/0.61             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.61  thf('63', plain,
% 0.40/0.61      (![X9 : $i, X10 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X9)
% 0.40/0.61          | ~ (v1_funct_1 @ X9)
% 0.40/0.61          | (r1_tarski @ (k2_relat_1 @ X9) @ (k1_relat_1 @ X10))
% 0.40/0.61          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X10)) != (k1_relat_1 @ X9))
% 0.40/0.61          | ~ (v1_funct_1 @ X10)
% 0.40/0.61          | ~ (v1_relat_1 @ X10))),
% 0.40/0.61      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.40/0.61  thf('64', plain,
% 0.40/0.61      ((((k1_relat_1 @ (k6_partfun1 @ sk_A)) != (k1_relat_1 @ sk_C))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_D)
% 0.40/0.61        | ~ (v1_funct_1 @ sk_D)
% 0.40/0.61        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))
% 0.40/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.40/0.61  thf(t71_relat_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.40/0.61       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.40/0.61  thf('65', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.40/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.40/0.61  thf('66', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.40/0.61  thf('67', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 0.40/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.61  thf('68', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.61  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('71', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('72', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.61         ((v1_relat_1 @ X14)
% 0.40/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.61  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.40/0.61  thf('74', plain,
% 0.40/0.61      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.40/0.61        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D)))),
% 0.40/0.61      inference('demod', [status(thm)], ['64', '67', '68', '69', '70', '73'])).
% 0.40/0.61  thf('75', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.40/0.61      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.40/0.61  thf(t44_relat_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ A ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( v1_relat_1 @ B ) =>
% 0.40/0.61           ( r1_tarski @
% 0.40/0.61             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.40/0.61  thf('76', plain,
% 0.40/0.61      (![X5 : $i, X6 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X5)
% 0.40/0.61          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.40/0.61             (k1_relat_1 @ X6))
% 0.40/0.61          | ~ (v1_relat_1 @ X6))),
% 0.40/0.61      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.40/0.61  thf(d10_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.61  thf('77', plain,
% 0.40/0.61      (![X0 : $i, X2 : $i]:
% 0.40/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.61  thf('78', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X0)
% 0.40/0.61          | ~ (v1_relat_1 @ X1)
% 0.40/0.61          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.40/0.61               (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.40/0.61          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.40/0.61  thf('79', plain,
% 0.40/0.61      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.40/0.61           (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 0.40/0.61        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_D)
% 0.40/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['75', '78'])).
% 0.40/0.61  thf('80', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 0.40/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.61  thf('81', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('82', plain,
% 0.40/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.61         ((v4_relat_1 @ X17 @ X18)
% 0.40/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.61  thf('83', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.40/0.61      inference('sup-', [status(thm)], ['81', '82'])).
% 0.40/0.61  thf(d18_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ B ) =>
% 0.40/0.61       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.61  thf('84', plain,
% 0.40/0.61      (![X3 : $i, X4 : $i]:
% 0.40/0.61         (~ (v4_relat_1 @ X3 @ X4)
% 0.40/0.61          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.40/0.61          | ~ (v1_relat_1 @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.40/0.61  thf('85', plain,
% 0.40/0.61      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['83', '84'])).
% 0.40/0.61  thf('86', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.40/0.61  thf('87', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.40/0.61      inference('demod', [status(thm)], ['85', '86'])).
% 0.40/0.61  thf('88', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.40/0.61      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.40/0.61  thf('89', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 0.40/0.61      inference('demod', [status(thm)], ['65', '66'])).
% 0.40/0.61  thf('90', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.61  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.40/0.61  thf('92', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.40/0.61      inference('demod', [status(thm)],
% 0.40/0.61                ['79', '80', '87', '88', '89', '90', '91'])).
% 0.40/0.61  thf('93', plain,
% 0.40/0.61      ((((sk_A) != (sk_A))
% 0.40/0.61        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D)))),
% 0.40/0.61      inference('demod', [status(thm)], ['74', '92'])).
% 0.40/0.61  thf('94', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))),
% 0.40/0.61      inference('simplify', [status(thm)], ['93'])).
% 0.40/0.61  thf(t47_funct_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.61           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.40/0.61               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.40/0.61             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.40/0.61  thf('95', plain,
% 0.40/0.61      (![X11 : $i, X12 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X11)
% 0.40/0.61          | ~ (v1_funct_1 @ X11)
% 0.40/0.61          | (v2_funct_1 @ X11)
% 0.40/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X11) @ (k1_relat_1 @ X12))
% 0.40/0.61          | ~ (v2_funct_1 @ (k5_relat_1 @ X11 @ X12))
% 0.40/0.61          | ~ (v1_funct_1 @ X12)
% 0.40/0.61          | ~ (v1_relat_1 @ X12))),
% 0.40/0.61      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.40/0.61  thf('96', plain,
% 0.40/0.61      ((~ (v1_relat_1 @ sk_D)
% 0.40/0.61        | ~ (v1_funct_1 @ sk_D)
% 0.40/0.61        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 0.40/0.61        | (v2_funct_1 @ sk_C)
% 0.40/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['94', '95'])).
% 0.40/0.61  thf('97', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.61  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('99', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.40/0.61      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.40/0.61  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.40/0.61  thf('100', plain, (![X13 : $i]: (v2_funct_1 @ (k6_relat_1 @ X13))),
% 0.40/0.61      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.40/0.61  thf('101', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.40/0.61  thf('102', plain, (![X13 : $i]: (v2_funct_1 @ (k6_partfun1 @ X13))),
% 0.40/0.61      inference('demod', [status(thm)], ['100', '101'])).
% 0.40/0.61  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.40/0.61  thf('105', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.61      inference('demod', [status(thm)],
% 0.40/0.61                ['96', '97', '98', '99', '102', '103', '104'])).
% 0.40/0.61  thf('106', plain, ($false), inference('demod', [status(thm)], ['52', '105'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
