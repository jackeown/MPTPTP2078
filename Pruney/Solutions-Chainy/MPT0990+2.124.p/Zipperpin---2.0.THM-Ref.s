%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3AW9uNczzS

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:15 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  298 (5257 expanded)
%              Number of leaves         :   50 (1643 expanded)
%              Depth                    :   40
%              Number of atoms          : 2799 (88836 expanded)
%              Number of equality atoms :  139 (5446 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t36_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
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
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 )
        = ( k5_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('21',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','22'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('25',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k10_relat_1 @ X18 @ X19 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X18 ) @ X19 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('32',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X6: $i] :
      ( ( ( k9_relat_1 @ X6 @ ( k1_relat_1 @ X6 ) )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('43',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','49','50','51','52'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X47: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['25','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['24','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ X21 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('69',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('70',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ X21 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('71',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k5_relat_1 @ X11 @ ( k5_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('80',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['23','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('82',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('83',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['81','82'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('84',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('90',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['85','90'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('92',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('93',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('96',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('97',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('98',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('99',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('100',plain,(
    ! [X47: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('101',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('112',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ( v4_relat_1 @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('123',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('124',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('125',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('126',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('127',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('140',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('141',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('142',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_partfun1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('146',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf('152',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ sk_B ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['146','147','148','149','150','151','156'])).

thf('158',plain,
    ( ( ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['122','157'])).

thf('159',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('160',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('167',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['158','165','166'])).

thf('168',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('169',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k5_relat_1 @ X11 @ ( k5_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('172',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_C )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['167','173'])).

thf('175',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ ( k6_partfun1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['121','177'])).

thf('179',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['158','165','166'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,
    ( ( ( k6_partfun1 @ sk_B )
      = ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['94','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('186',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k7_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X2 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X2 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X2 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ ( k7_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['186','192'])).

thf('194',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['91','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('196',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('198',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('199',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('200',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('202',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k7_relat_1 @ sk_D @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['197','202'])).

thf('204',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['28','29'])).

thf('205',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['85','90'])).

thf('206',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('207',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['203','204','205','206','207','208'])).

thf('210',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['196','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('212',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('213',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_D ) @ X0 )
        = ( k5_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['210','213'])).

thf('215',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('216',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('217',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('218',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['196','209'])).

thf('219',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['196','209'])).

thf('220',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X0 ) @ sk_D )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('223',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ X0 ) @ sk_D )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['214','215','216','217','218','224'])).

thf('226',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['85','90'])).

thf('227',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('229',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('231',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('233',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('235',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','49','50','51','52'])).

thf('236',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_partfun1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['234','237'])).

thf('239',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('240',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['233','241'])).

thf('243',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('244',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','225','226','242','243'])).

thf('245',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['244','245'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3AW9uNczzS
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:25:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.65/1.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.65/1.91  % Solved by: fo/fo7.sh
% 1.65/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.91  % done 1722 iterations in 1.438s
% 1.65/1.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.65/1.91  % SZS output start Refutation
% 1.65/1.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.91  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.65/1.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.91  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.91  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.65/1.91  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.65/1.91  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.65/1.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.91  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.65/1.91  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.65/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.91  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.65/1.91  thf(sk_D_type, type, sk_D: $i).
% 1.65/1.91  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.65/1.91  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.65/1.91  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.65/1.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.65/1.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.91  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.65/1.91  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.65/1.91  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.65/1.91  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.91  thf(t36_funct_2, conjecture,
% 1.65/1.91    (![A:$i,B:$i,C:$i]:
% 1.65/1.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.91       ( ![D:$i]:
% 1.65/1.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.91           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.65/1.91               ( r2_relset_1 @
% 1.65/1.91                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.65/1.91                 ( k6_partfun1 @ A ) ) & 
% 1.65/1.91               ( v2_funct_1 @ C ) ) =>
% 1.65/1.91             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.65/1.91               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.65/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.91    (~( ![A:$i,B:$i,C:$i]:
% 1.65/1.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.91          ( ![D:$i]:
% 1.65/1.91            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.91                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.91              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.65/1.91                  ( r2_relset_1 @
% 1.65/1.91                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.65/1.91                    ( k6_partfun1 @ A ) ) & 
% 1.65/1.91                  ( v2_funct_1 @ C ) ) =>
% 1.65/1.91                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.65/1.91                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.65/1.91    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.65/1.91  thf('0', plain,
% 1.65/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('1', plain,
% 1.65/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf(redefinition_k1_partfun1, axiom,
% 1.65/1.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.91     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.91         ( v1_funct_1 @ F ) & 
% 1.65/1.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.65/1.91       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.65/1.91  thf('2', plain,
% 1.65/1.91      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.65/1.91         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.65/1.91          | ~ (v1_funct_1 @ X40)
% 1.65/1.91          | ~ (v1_funct_1 @ X43)
% 1.65/1.91          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.65/1.91          | ((k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43)
% 1.65/1.91              = (k5_relat_1 @ X40 @ X43)))),
% 1.65/1.91      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.65/1.91  thf('3', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.65/1.91            = (k5_relat_1 @ sk_C @ X0))
% 1.65/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ sk_C))),
% 1.65/1.91      inference('sup-', [status(thm)], ['1', '2'])).
% 1.65/1.91  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('5', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.65/1.91            = (k5_relat_1 @ sk_C @ X0))
% 1.65/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.91          | ~ (v1_funct_1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['3', '4'])).
% 1.65/1.91  thf('6', plain,
% 1.65/1.91      ((~ (v1_funct_1 @ sk_D)
% 1.65/1.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.91            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['0', '5'])).
% 1.65/1.91  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('8', plain,
% 1.65/1.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.65/1.91        (k6_partfun1 @ sk_A))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('9', plain,
% 1.65/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('10', plain,
% 1.65/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf(dt_k1_partfun1, axiom,
% 1.65/1.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.91     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.91         ( v1_funct_1 @ F ) & 
% 1.65/1.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.65/1.91       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.65/1.91         ( m1_subset_1 @
% 1.65/1.91           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.65/1.91           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.65/1.91  thf('11', plain,
% 1.65/1.91      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.65/1.91         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.65/1.91          | ~ (v1_funct_1 @ X32)
% 1.65/1.91          | ~ (v1_funct_1 @ X35)
% 1.65/1.91          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.65/1.91          | (m1_subset_1 @ (k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35) @ 
% 1.65/1.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X37))))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.65/1.91  thf('12', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.65/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.91          | ~ (v1_funct_1 @ X1)
% 1.65/1.91          | ~ (v1_funct_1 @ sk_C))),
% 1.65/1.91      inference('sup-', [status(thm)], ['10', '11'])).
% 1.65/1.91  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('14', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.65/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.91          | ~ (v1_funct_1 @ X1))),
% 1.65/1.91      inference('demod', [status(thm)], ['12', '13'])).
% 1.65/1.91  thf('15', plain,
% 1.65/1.91      ((~ (v1_funct_1 @ sk_D)
% 1.65/1.91        | (m1_subset_1 @ 
% 1.65/1.91           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.65/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.91      inference('sup-', [status(thm)], ['9', '14'])).
% 1.65/1.91  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('17', plain,
% 1.65/1.91      ((m1_subset_1 @ 
% 1.65/1.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.65/1.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.65/1.91      inference('demod', [status(thm)], ['15', '16'])).
% 1.65/1.91  thf(redefinition_r2_relset_1, axiom,
% 1.65/1.91    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.91     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.91       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.65/1.91  thf('18', plain,
% 1.65/1.91      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.65/1.91         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.65/1.91          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.65/1.91          | ((X28) = (X31))
% 1.65/1.91          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 1.65/1.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.65/1.91  thf('19', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.91             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.65/1.91          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.65/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.91      inference('sup-', [status(thm)], ['17', '18'])).
% 1.65/1.91  thf('20', plain,
% 1.65/1.91      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.65/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.65/1.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.91            = (k6_partfun1 @ sk_A)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['8', '19'])).
% 1.65/1.91  thf(dt_k6_partfun1, axiom,
% 1.65/1.91    (![A:$i]:
% 1.65/1.91     ( ( m1_subset_1 @
% 1.65/1.91         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.65/1.91       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.65/1.91  thf('21', plain,
% 1.65/1.91      (![X39 : $i]:
% 1.65/1.91         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 1.65/1.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.65/1.91  thf('22', plain,
% 1.65/1.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.91         = (k6_partfun1 @ sk_A))),
% 1.65/1.91      inference('demod', [status(thm)], ['20', '21'])).
% 1.65/1.91  thf('23', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.65/1.91      inference('demod', [status(thm)], ['6', '7', '22'])).
% 1.65/1.91  thf(dt_k2_funct_1, axiom,
% 1.65/1.91    (![A:$i]:
% 1.65/1.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.91       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.65/1.91         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.65/1.91  thf('24', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf('25', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf('26', plain,
% 1.65/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf(redefinition_k2_relset_1, axiom,
% 1.65/1.91    (![A:$i,B:$i,C:$i]:
% 1.65/1.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.65/1.91  thf('27', plain,
% 1.65/1.91      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.65/1.91         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 1.65/1.91          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.65/1.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.91  thf('28', plain,
% 1.65/1.91      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.65/1.91      inference('sup-', [status(thm)], ['26', '27'])).
% 1.65/1.91  thf('29', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('30', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.91      inference('sup+', [status(thm)], ['28', '29'])).
% 1.65/1.91  thf(t155_funct_1, axiom,
% 1.65/1.91    (![A:$i,B:$i]:
% 1.65/1.91     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.65/1.91       ( ( v2_funct_1 @ B ) =>
% 1.65/1.91         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.65/1.91  thf('31', plain,
% 1.65/1.91      (![X18 : $i, X19 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X18)
% 1.65/1.91          | ((k10_relat_1 @ X18 @ X19)
% 1.65/1.91              = (k9_relat_1 @ (k2_funct_1 @ X18) @ X19))
% 1.65/1.91          | ~ (v1_funct_1 @ X18)
% 1.65/1.91          | ~ (v1_relat_1 @ X18))),
% 1.65/1.91      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.65/1.91  thf('32', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf(t55_funct_1, axiom,
% 1.65/1.91    (![A:$i]:
% 1.65/1.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.91       ( ( v2_funct_1 @ A ) =>
% 1.65/1.91         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.65/1.91           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.65/1.91  thf('33', plain,
% 1.65/1.91      (![X20 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X20)
% 1.65/1.91          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.65/1.91          | ~ (v1_funct_1 @ X20)
% 1.65/1.91          | ~ (v1_relat_1 @ X20))),
% 1.65/1.91      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.91  thf(t146_relat_1, axiom,
% 1.65/1.91    (![A:$i]:
% 1.65/1.91     ( ( v1_relat_1 @ A ) =>
% 1.65/1.91       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.65/1.91  thf('34', plain,
% 1.65/1.91      (![X6 : $i]:
% 1.65/1.91         (((k9_relat_1 @ X6 @ (k1_relat_1 @ X6)) = (k2_relat_1 @ X6))
% 1.65/1.91          | ~ (v1_relat_1 @ X6))),
% 1.65/1.91      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.65/1.91  thf('35', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.91            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.65/1.91      inference('sup+', [status(thm)], ['33', '34'])).
% 1.65/1.91  thf('36', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.91              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.65/1.91      inference('sup-', [status(thm)], ['32', '35'])).
% 1.65/1.91  thf('37', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.91            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['36'])).
% 1.65/1.91  thf('38', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 1.65/1.91            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0))),
% 1.65/1.91      inference('sup+', [status(thm)], ['31', '37'])).
% 1.65/1.91  thf('39', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 1.65/1.91              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.65/1.91      inference('simplify', [status(thm)], ['38'])).
% 1.65/1.91  thf('40', plain,
% 1.65/1.91      ((((k10_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.65/1.91        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.91        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.91        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.91      inference('sup+', [status(thm)], ['30', '39'])).
% 1.65/1.91  thf('41', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.91      inference('sup+', [status(thm)], ['28', '29'])).
% 1.65/1.91  thf(t169_relat_1, axiom,
% 1.65/1.91    (![A:$i]:
% 1.65/1.91     ( ( v1_relat_1 @ A ) =>
% 1.65/1.91       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.65/1.91  thf('42', plain,
% 1.65/1.91      (![X7 : $i]:
% 1.65/1.91         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 1.65/1.91          | ~ (v1_relat_1 @ X7))),
% 1.65/1.91      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.65/1.91  thf('43', plain,
% 1.65/1.91      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 1.65/1.91        | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.91      inference('sup+', [status(thm)], ['41', '42'])).
% 1.65/1.91  thf('44', plain,
% 1.65/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf(cc2_relat_1, axiom,
% 1.65/1.91    (![A:$i]:
% 1.65/1.91     ( ( v1_relat_1 @ A ) =>
% 1.65/1.91       ( ![B:$i]:
% 1.65/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.65/1.91  thf('45', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i]:
% 1.65/1.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.65/1.91          | (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X1))),
% 1.65/1.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.91  thf('46', plain,
% 1.65/1.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.65/1.91      inference('sup-', [status(thm)], ['44', '45'])).
% 1.65/1.91  thf(fc6_relat_1, axiom,
% 1.65/1.91    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.65/1.91  thf('47', plain,
% 1.65/1.91      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.65/1.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.91  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('49', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 1.65/1.91      inference('demod', [status(thm)], ['43', '48'])).
% 1.65/1.91  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('53', plain,
% 1.65/1.91      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.91      inference('demod', [status(thm)], ['40', '49', '50', '51', '52'])).
% 1.65/1.91  thf(t3_funct_2, axiom,
% 1.65/1.91    (![A:$i]:
% 1.65/1.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.91       ( ( v1_funct_1 @ A ) & 
% 1.65/1.91         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.65/1.91         ( m1_subset_1 @
% 1.65/1.91           A @ 
% 1.65/1.91           ( k1_zfmisc_1 @
% 1.65/1.91             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.65/1.91  thf('54', plain,
% 1.65/1.91      (![X47 : $i]:
% 1.65/1.91         ((m1_subset_1 @ X47 @ 
% 1.65/1.91           (k1_zfmisc_1 @ 
% 1.65/1.91            (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))))
% 1.65/1.91          | ~ (v1_funct_1 @ X47)
% 1.65/1.91          | ~ (v1_relat_1 @ X47))),
% 1.65/1.91      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.65/1.91  thf('55', plain,
% 1.65/1.91      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.91         (k1_zfmisc_1 @ 
% 1.65/1.91          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.65/1.91           (k1_relat_1 @ sk_C))))
% 1.65/1.91        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.91        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.91      inference('sup+', [status(thm)], ['53', '54'])).
% 1.65/1.91  thf('56', plain,
% 1.65/1.91      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.91        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.91        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.91        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.91           (k1_zfmisc_1 @ 
% 1.65/1.91            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.65/1.91             (k1_relat_1 @ sk_C)))))),
% 1.65/1.91      inference('sup-', [status(thm)], ['25', '55'])).
% 1.65/1.91  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('59', plain,
% 1.65/1.91      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.91        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.91           (k1_zfmisc_1 @ 
% 1.65/1.91            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.65/1.91             (k1_relat_1 @ sk_C)))))),
% 1.65/1.91      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.65/1.91  thf('60', plain,
% 1.65/1.91      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.91        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.91        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.91           (k1_zfmisc_1 @ 
% 1.65/1.91            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.65/1.91             (k1_relat_1 @ sk_C)))))),
% 1.65/1.91      inference('sup-', [status(thm)], ['24', '59'])).
% 1.65/1.91  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('63', plain,
% 1.65/1.91      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.91        (k1_zfmisc_1 @ 
% 1.65/1.91         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.65/1.91          (k1_relat_1 @ sk_C))))),
% 1.65/1.91      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.65/1.91  thf('64', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i]:
% 1.65/1.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.65/1.91          | (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X1))),
% 1.65/1.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.91  thf('65', plain,
% 1.65/1.91      ((~ (v1_relat_1 @ 
% 1.65/1.91           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.65/1.91            (k1_relat_1 @ sk_C)))
% 1.65/1.91        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.91  thf('66', plain,
% 1.65/1.91      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.65/1.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.91  thf('67', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.65/1.91      inference('demod', [status(thm)], ['65', '66'])).
% 1.65/1.91  thf(t61_funct_1, axiom,
% 1.65/1.91    (![A:$i]:
% 1.65/1.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.91       ( ( v2_funct_1 @ A ) =>
% 1.65/1.91         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.65/1.91             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.65/1.91           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.65/1.91             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.65/1.91  thf('68', plain,
% 1.65/1.91      (![X21 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X21)
% 1.65/1.91          | ((k5_relat_1 @ (k2_funct_1 @ X21) @ X21)
% 1.65/1.91              = (k6_relat_1 @ (k2_relat_1 @ X21)))
% 1.65/1.91          | ~ (v1_funct_1 @ X21)
% 1.65/1.91          | ~ (v1_relat_1 @ X21))),
% 1.65/1.91      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.65/1.91  thf(redefinition_k6_partfun1, axiom,
% 1.65/1.91    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.65/1.91  thf('69', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 1.65/1.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.91  thf('70', plain,
% 1.65/1.91      (![X21 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X21)
% 1.65/1.91          | ((k5_relat_1 @ (k2_funct_1 @ X21) @ X21)
% 1.65/1.91              = (k6_partfun1 @ (k2_relat_1 @ X21)))
% 1.65/1.91          | ~ (v1_funct_1 @ X21)
% 1.65/1.91          | ~ (v1_relat_1 @ X21))),
% 1.65/1.91      inference('demod', [status(thm)], ['68', '69'])).
% 1.65/1.91  thf(t55_relat_1, axiom,
% 1.65/1.91    (![A:$i]:
% 1.65/1.91     ( ( v1_relat_1 @ A ) =>
% 1.65/1.91       ( ![B:$i]:
% 1.65/1.91         ( ( v1_relat_1 @ B ) =>
% 1.65/1.91           ( ![C:$i]:
% 1.65/1.91             ( ( v1_relat_1 @ C ) =>
% 1.65/1.91               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.65/1.91                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.65/1.91  thf('71', plain,
% 1.65/1.91      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X10)
% 1.65/1.91          | ((k5_relat_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 1.65/1.91              = (k5_relat_1 @ X11 @ (k5_relat_1 @ X10 @ X12)))
% 1.65/1.91          | ~ (v1_relat_1 @ X12)
% 1.65/1.91          | ~ (v1_relat_1 @ X11))),
% 1.65/1.91      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.65/1.91  thf('72', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.65/1.91            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | ~ (v1_relat_1 @ X1)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('sup+', [status(thm)], ['70', '71'])).
% 1.65/1.91  thf('73', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X1)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.65/1.91              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 1.65/1.91      inference('simplify', [status(thm)], ['72'])).
% 1.65/1.91  thf('74', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ X0)
% 1.65/1.91            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.65/1.91          | ~ (v1_relat_1 @ sk_C)
% 1.65/1.91          | ~ (v1_funct_1 @ sk_C)
% 1.65/1.91          | ~ (v2_funct_1 @ sk_C)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('sup-', [status(thm)], ['67', '73'])).
% 1.65/1.91  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.91      inference('sup+', [status(thm)], ['28', '29'])).
% 1.65/1.91  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('79', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.65/1.91            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 1.65/1.91  thf('80', plain,
% 1.65/1.91      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.65/1.91          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.65/1.91        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.91      inference('sup+', [status(thm)], ['23', '79'])).
% 1.65/1.91  thf('81', plain,
% 1.65/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf(cc2_relset_1, axiom,
% 1.65/1.91    (![A:$i,B:$i,C:$i]:
% 1.65/1.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.91       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.65/1.91  thf('82', plain,
% 1.65/1.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.91         ((v4_relat_1 @ X22 @ X23)
% 1.65/1.91          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.91  thf('83', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.65/1.91      inference('sup-', [status(thm)], ['81', '82'])).
% 1.65/1.91  thf(t209_relat_1, axiom,
% 1.65/1.91    (![A:$i,B:$i]:
% 1.65/1.91     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.65/1.91       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.65/1.91  thf('84', plain,
% 1.65/1.91      (![X8 : $i, X9 : $i]:
% 1.65/1.91         (((X8) = (k7_relat_1 @ X8 @ X9))
% 1.65/1.91          | ~ (v4_relat_1 @ X8 @ X9)
% 1.65/1.91          | ~ (v1_relat_1 @ X8))),
% 1.65/1.91      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.65/1.91  thf('85', plain,
% 1.65/1.91      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['83', '84'])).
% 1.65/1.91  thf('86', plain,
% 1.65/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('87', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i]:
% 1.65/1.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.65/1.91          | (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X1))),
% 1.65/1.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.91  thf('88', plain,
% 1.65/1.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.65/1.91      inference('sup-', [status(thm)], ['86', '87'])).
% 1.65/1.91  thf('89', plain,
% 1.65/1.91      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.65/1.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.91  thf('90', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.91      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.91  thf('91', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.65/1.91      inference('demod', [status(thm)], ['85', '90'])).
% 1.65/1.91  thf(t94_relat_1, axiom,
% 1.65/1.91    (![A:$i,B:$i]:
% 1.65/1.91     ( ( v1_relat_1 @ B ) =>
% 1.65/1.91       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.65/1.91  thf('92', plain,
% 1.65/1.91      (![X15 : $i, X16 : $i]:
% 1.65/1.91         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 1.65/1.91          | ~ (v1_relat_1 @ X16))),
% 1.65/1.91      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.65/1.91  thf('93', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 1.65/1.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.91  thf('94', plain,
% 1.65/1.91      (![X15 : $i, X16 : $i]:
% 1.65/1.91         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.65/1.91          | ~ (v1_relat_1 @ X16))),
% 1.65/1.91      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.91  thf('95', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf('96', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf('97', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf('98', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf('99', plain,
% 1.65/1.91      (![X20 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X20)
% 1.65/1.91          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.65/1.91          | ~ (v1_funct_1 @ X20)
% 1.65/1.91          | ~ (v1_relat_1 @ X20))),
% 1.65/1.91      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.91  thf('100', plain,
% 1.65/1.91      (![X47 : $i]:
% 1.65/1.91         ((m1_subset_1 @ X47 @ 
% 1.65/1.91           (k1_zfmisc_1 @ 
% 1.65/1.91            (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))))
% 1.65/1.91          | ~ (v1_funct_1 @ X47)
% 1.65/1.91          | ~ (v1_relat_1 @ X47))),
% 1.65/1.91      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.65/1.91  thf('101', plain,
% 1.65/1.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.91         ((v4_relat_1 @ X22 @ X23)
% 1.65/1.91          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.91  thf('102', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['100', '101'])).
% 1.65/1.91  thf(d18_relat_1, axiom,
% 1.65/1.91    (![A:$i,B:$i]:
% 1.65/1.91     ( ( v1_relat_1 @ B ) =>
% 1.65/1.91       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.65/1.91  thf('103', plain,
% 1.65/1.91      (![X2 : $i, X3 : $i]:
% 1.65/1.91         (~ (v4_relat_1 @ X2 @ X3)
% 1.65/1.91          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 1.65/1.91          | ~ (v1_relat_1 @ X2))),
% 1.65/1.91      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.91  thf('104', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['102', '103'])).
% 1.65/1.91  thf('105', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['104'])).
% 1.65/1.91  thf('106', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.65/1.91      inference('sup+', [status(thm)], ['99', '105'])).
% 1.65/1.91  thf('107', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 1.65/1.91      inference('sup-', [status(thm)], ['98', '106'])).
% 1.65/1.91  thf('108', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['107'])).
% 1.65/1.91  thf('109', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 1.65/1.91      inference('sup-', [status(thm)], ['97', '108'])).
% 1.65/1.91  thf('110', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['109'])).
% 1.65/1.91  thf('111', plain,
% 1.65/1.91      (![X20 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X20)
% 1.65/1.91          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.65/1.91          | ~ (v1_funct_1 @ X20)
% 1.65/1.91          | ~ (v1_relat_1 @ X20))),
% 1.65/1.91      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.91  thf('112', plain,
% 1.65/1.91      (![X2 : $i, X3 : $i]:
% 1.65/1.91         (~ (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 1.65/1.91          | (v4_relat_1 @ X2 @ X3)
% 1.65/1.91          | ~ (v1_relat_1 @ X2))),
% 1.65/1.91      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.91  thf('113', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i]:
% 1.65/1.91         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | (v4_relat_1 @ (k2_funct_1 @ X0) @ X1))),
% 1.65/1.91      inference('sup-', [status(thm)], ['111', '112'])).
% 1.65/1.91  thf('114', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('sup-', [status(thm)], ['110', '113'])).
% 1.65/1.91  thf('115', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['114'])).
% 1.65/1.91  thf('116', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 1.65/1.91      inference('sup-', [status(thm)], ['96', '115'])).
% 1.65/1.91  thf('117', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['116'])).
% 1.65/1.91  thf('118', plain,
% 1.65/1.91      (![X8 : $i, X9 : $i]:
% 1.65/1.91         (((X8) = (k7_relat_1 @ X8 @ X9))
% 1.65/1.91          | ~ (v4_relat_1 @ X8 @ X9)
% 1.65/1.91          | ~ (v1_relat_1 @ X8))),
% 1.65/1.91      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.65/1.91  thf('119', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | ((k2_funct_1 @ X0)
% 1.65/1.91              = (k7_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.65/1.91                 (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.65/1.91      inference('sup-', [status(thm)], ['117', '118'])).
% 1.65/1.91  thf('120', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ((k2_funct_1 @ X0)
% 1.65/1.91              = (k7_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.65/1.91                 (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('sup-', [status(thm)], ['95', '119'])).
% 1.65/1.91  thf('121', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X0)
% 1.65/1.91          | ((k2_funct_1 @ X0)
% 1.65/1.91              = (k7_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.65/1.91                 (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['120'])).
% 1.65/1.91  thf('122', plain,
% 1.65/1.91      (![X15 : $i, X16 : $i]:
% 1.65/1.91         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.65/1.91          | ~ (v1_relat_1 @ X16))),
% 1.65/1.91      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.91  thf('123', plain,
% 1.65/1.91      (![X20 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X20)
% 1.65/1.91          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.65/1.91          | ~ (v1_funct_1 @ X20)
% 1.65/1.91          | ~ (v1_relat_1 @ X20))),
% 1.65/1.91      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.91  thf('124', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf('125', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf('126', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf('127', plain,
% 1.65/1.91      (![X20 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X20)
% 1.65/1.91          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.65/1.91          | ~ (v1_funct_1 @ X20)
% 1.65/1.91          | ~ (v1_relat_1 @ X20))),
% 1.65/1.91      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.91  thf('128', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['100', '101'])).
% 1.65/1.91  thf('129', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.65/1.91      inference('sup+', [status(thm)], ['127', '128'])).
% 1.65/1.91  thf('130', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['126', '129'])).
% 1.65/1.91  thf('131', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['130'])).
% 1.65/1.91  thf('132', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['125', '131'])).
% 1.65/1.91  thf('133', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['132'])).
% 1.65/1.91  thf('134', plain,
% 1.65/1.91      (![X2 : $i, X3 : $i]:
% 1.65/1.91         (~ (v4_relat_1 @ X2 @ X3)
% 1.65/1.91          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 1.65/1.91          | ~ (v1_relat_1 @ X2))),
% 1.65/1.91      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.91  thf('135', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.65/1.91          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['133', '134'])).
% 1.65/1.91  thf('136', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('sup-', [status(thm)], ['124', '135'])).
% 1.65/1.91  thf('137', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X0)
% 1.65/1.91          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['136'])).
% 1.65/1.91  thf('138', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0))),
% 1.65/1.91      inference('sup+', [status(thm)], ['123', '137'])).
% 1.65/1.91  thf('139', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.65/1.91      inference('simplify', [status(thm)], ['138'])).
% 1.65/1.91  thf(t79_relat_1, axiom,
% 1.65/1.91    (![A:$i,B:$i]:
% 1.65/1.91     ( ( v1_relat_1 @ B ) =>
% 1.65/1.91       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.65/1.91         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.65/1.91  thf('140', plain,
% 1.65/1.91      (![X13 : $i, X14 : $i]:
% 1.65/1.91         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 1.65/1.91          | ((k5_relat_1 @ X13 @ (k6_relat_1 @ X14)) = (X13))
% 1.65/1.91          | ~ (v1_relat_1 @ X13))),
% 1.65/1.91      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.65/1.91  thf('141', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 1.65/1.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.91  thf('142', plain,
% 1.65/1.91      (![X13 : $i, X14 : $i]:
% 1.65/1.91         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 1.65/1.91          | ((k5_relat_1 @ X13 @ (k6_partfun1 @ X14)) = (X13))
% 1.65/1.91          | ~ (v1_relat_1 @ X13))),
% 1.65/1.91      inference('demod', [status(thm)], ['140', '141'])).
% 1.65/1.91  thf('143', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['139', '142'])).
% 1.65/1.91  thf('144', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0))
% 1.65/1.91          | ~ (v2_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_funct_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('simplify', [status(thm)], ['143'])).
% 1.65/1.91  thf('145', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.65/1.91            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 1.65/1.91  thf('146', plain,
% 1.65/1.91      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.65/1.91          (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.65/1.91          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.65/1.91        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.91        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.91        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.91        | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C))))),
% 1.65/1.91      inference('sup+', [status(thm)], ['144', '145'])).
% 1.65/1.91  thf('147', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.91      inference('sup+', [status(thm)], ['28', '29'])).
% 1.65/1.91  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('150', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('151', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.91      inference('sup+', [status(thm)], ['28', '29'])).
% 1.65/1.91  thf('152', plain,
% 1.65/1.91      (![X39 : $i]:
% 1.65/1.91         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 1.65/1.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.65/1.91  thf('153', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i]:
% 1.65/1.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.65/1.91          | (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ X1))),
% 1.65/1.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.91  thf('154', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.65/1.91          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['152', '153'])).
% 1.65/1.91  thf('155', plain,
% 1.65/1.91      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.65/1.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.91  thf('156', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['154', '155'])).
% 1.65/1.91  thf('157', plain,
% 1.65/1.91      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k6_partfun1 @ sk_B))
% 1.65/1.91         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.65/1.91      inference('demod', [status(thm)],
% 1.65/1.91                ['146', '147', '148', '149', '150', '151', '156'])).
% 1.65/1.91  thf('158', plain,
% 1.65/1.91      ((((k7_relat_1 @ (k6_partfun1 @ sk_B) @ sk_B)
% 1.65/1.91          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.65/1.91        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.65/1.91      inference('sup+', [status(thm)], ['122', '157'])).
% 1.65/1.91  thf('159', plain,
% 1.65/1.91      (![X39 : $i]:
% 1.65/1.91         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 1.65/1.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.65/1.91  thf('160', plain,
% 1.65/1.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.91         ((v4_relat_1 @ X22 @ X23)
% 1.65/1.91          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.91  thf('161', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 1.65/1.91      inference('sup-', [status(thm)], ['159', '160'])).
% 1.65/1.91  thf('162', plain,
% 1.65/1.91      (![X8 : $i, X9 : $i]:
% 1.65/1.91         (((X8) = (k7_relat_1 @ X8 @ X9))
% 1.65/1.91          | ~ (v4_relat_1 @ X8 @ X9)
% 1.65/1.91          | ~ (v1_relat_1 @ X8))),
% 1.65/1.91      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.65/1.91  thf('163', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.65/1.91          | ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['161', '162'])).
% 1.65/1.91  thf('164', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['154', '155'])).
% 1.65/1.91  thf('165', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['163', '164'])).
% 1.65/1.91  thf('166', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['154', '155'])).
% 1.65/1.91  thf('167', plain,
% 1.65/1.91      (((k6_partfun1 @ sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.65/1.91      inference('demod', [status(thm)], ['158', '165', '166'])).
% 1.65/1.91  thf('168', plain,
% 1.65/1.91      (![X15 : $i, X16 : $i]:
% 1.65/1.91         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.65/1.91          | ~ (v1_relat_1 @ X16))),
% 1.65/1.91      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.91  thf('169', plain,
% 1.65/1.91      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X10)
% 1.65/1.91          | ((k5_relat_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 1.65/1.91              = (k5_relat_1 @ X11 @ (k5_relat_1 @ X10 @ X12)))
% 1.65/1.91          | ~ (v1_relat_1 @ X12)
% 1.65/1.91          | ~ (v1_relat_1 @ X11))),
% 1.65/1.91      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.65/1.91  thf('170', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.65/1.91            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 1.65/1.91          | ~ (v1_relat_1 @ X1)
% 1.65/1.91          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.65/1.91          | ~ (v1_relat_1 @ X2)
% 1.65/1.91          | ~ (v1_relat_1 @ X1))),
% 1.65/1.91      inference('sup+', [status(thm)], ['168', '169'])).
% 1.65/1.91  thf('171', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['154', '155'])).
% 1.65/1.91  thf('172', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.65/1.91            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 1.65/1.91          | ~ (v1_relat_1 @ X1)
% 1.65/1.91          | ~ (v1_relat_1 @ X2)
% 1.65/1.91          | ~ (v1_relat_1 @ X1))),
% 1.65/1.91      inference('demod', [status(thm)], ['170', '171'])).
% 1.65/1.91  thf('173', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X2)
% 1.65/1.91          | ~ (v1_relat_1 @ X1)
% 1.65/1.91          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.65/1.91              = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 1.65/1.91      inference('simplify', [status(thm)], ['172'])).
% 1.65/1.91  thf('174', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_C)
% 1.65/1.91            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ sk_B)))
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.91          | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.91      inference('sup+', [status(thm)], ['167', '173'])).
% 1.65/1.91  thf('175', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.65/1.91      inference('demod', [status(thm)], ['65', '66'])).
% 1.65/1.91  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('177', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((k5_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_C)
% 1.65/1.91           = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ sk_B)))),
% 1.65/1.91      inference('demod', [status(thm)], ['174', '175', '176'])).
% 1.65/1.91  thf('178', plain,
% 1.65/1.91      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.65/1.91          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91             (k6_partfun1 @ sk_B)))
% 1.65/1.91        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.91        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.91        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.91      inference('sup+', [status(thm)], ['121', '177'])).
% 1.65/1.91  thf('179', plain,
% 1.65/1.91      (((k6_partfun1 @ sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.65/1.91      inference('demod', [status(thm)], ['158', '165', '166'])).
% 1.65/1.91  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('183', plain,
% 1.65/1.91      (((k6_partfun1 @ sk_B)
% 1.65/1.91         = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91            (k6_partfun1 @ sk_B)))),
% 1.65/1.91      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 1.65/1.91  thf('184', plain,
% 1.65/1.91      ((((k6_partfun1 @ sk_B)
% 1.65/1.91          = (k7_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.65/1.91             (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.65/1.91        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.65/1.91      inference('sup+', [status(thm)], ['94', '183'])).
% 1.65/1.91  thf('185', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['154', '155'])).
% 1.65/1.91  thf('186', plain,
% 1.65/1.91      (((k6_partfun1 @ sk_B)
% 1.65/1.91         = (k7_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.65/1.91            (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.65/1.91      inference('demod', [status(thm)], ['184', '185'])).
% 1.65/1.91  thf('187', plain,
% 1.65/1.91      (![X15 : $i, X16 : $i]:
% 1.65/1.91         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.65/1.91          | ~ (v1_relat_1 @ X16))),
% 1.65/1.91      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.91  thf('188', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X2)
% 1.65/1.91          | ~ (v1_relat_1 @ X1)
% 1.65/1.91          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.65/1.91              = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 1.65/1.91      inference('simplify', [status(thm)], ['172'])).
% 1.65/1.91  thf('189', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ X0) @ X2) @ X1)
% 1.65/1.91            = (k5_relat_1 @ (k6_partfun1 @ X2) @ (k7_relat_1 @ X1 @ X0)))
% 1.65/1.91          | ~ (v1_relat_1 @ X1)
% 1.65/1.91          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.65/1.91          | ~ (v1_relat_1 @ X1))),
% 1.65/1.91      inference('sup+', [status(thm)], ['187', '188'])).
% 1.65/1.91  thf('190', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['154', '155'])).
% 1.65/1.91  thf('191', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ X0) @ X2) @ X1)
% 1.65/1.91            = (k5_relat_1 @ (k6_partfun1 @ X2) @ (k7_relat_1 @ X1 @ X0)))
% 1.65/1.91          | ~ (v1_relat_1 @ X1)
% 1.65/1.91          | ~ (v1_relat_1 @ X1))),
% 1.65/1.91      inference('demod', [status(thm)], ['189', '190'])).
% 1.65/1.91  thf('192', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X1)
% 1.65/1.91          | ((k5_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ X0) @ X2) @ X1)
% 1.65/1.91              = (k5_relat_1 @ (k6_partfun1 @ X2) @ (k7_relat_1 @ X1 @ X0))))),
% 1.65/1.91      inference('simplify', [status(thm)], ['191'])).
% 1.65/1.91  thf('193', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.65/1.91            = (k5_relat_1 @ 
% 1.65/1.91               (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91               (k7_relat_1 @ X0 @ sk_B)))
% 1.65/1.91          | ~ (v1_relat_1 @ X0))),
% 1.65/1.91      inference('sup+', [status(thm)], ['186', '192'])).
% 1.65/1.91  thf('194', plain,
% 1.65/1.91      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.65/1.91          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91             sk_D))
% 1.65/1.91        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.91      inference('sup+', [status(thm)], ['91', '193'])).
% 1.65/1.91  thf('195', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.91      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.91  thf('196', plain,
% 1.65/1.91      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.65/1.91         = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91            sk_D))),
% 1.65/1.91      inference('demod', [status(thm)], ['194', '195'])).
% 1.65/1.91  thf('197', plain,
% 1.65/1.91      (![X20 : $i]:
% 1.65/1.91         (~ (v2_funct_1 @ X20)
% 1.65/1.91          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.65/1.91          | ~ (v1_funct_1 @ X20)
% 1.65/1.91          | ~ (v1_relat_1 @ X20))),
% 1.65/1.91      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.91  thf('198', plain,
% 1.65/1.91      (![X15 : $i, X16 : $i]:
% 1.65/1.91         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.65/1.91          | ~ (v1_relat_1 @ X16))),
% 1.65/1.91      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.91  thf('199', plain,
% 1.65/1.91      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.65/1.91         = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91            sk_D))),
% 1.65/1.91      inference('demod', [status(thm)], ['194', '195'])).
% 1.65/1.91  thf('200', plain,
% 1.65/1.91      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.65/1.91          = (k7_relat_1 @ sk_D @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.65/1.91        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.91      inference('sup+', [status(thm)], ['198', '199'])).
% 1.65/1.91  thf('201', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.91      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.91  thf('202', plain,
% 1.65/1.91      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.65/1.91         = (k7_relat_1 @ sk_D @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.65/1.91      inference('demod', [status(thm)], ['200', '201'])).
% 1.65/1.91  thf('203', plain,
% 1.65/1.91      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.65/1.91          = (k7_relat_1 @ sk_D @ (k2_relat_1 @ sk_C)))
% 1.65/1.91        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.91        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.91        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.91      inference('sup+', [status(thm)], ['197', '202'])).
% 1.65/1.91  thf('204', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.91      inference('sup+', [status(thm)], ['28', '29'])).
% 1.65/1.91  thf('205', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.65/1.91      inference('demod', [status(thm)], ['85', '90'])).
% 1.65/1.91  thf('206', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('207', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('208', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('209', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.65/1.91      inference('demod', [status(thm)],
% 1.65/1.91                ['203', '204', '205', '206', '207', '208'])).
% 1.65/1.91  thf('210', plain,
% 1.65/1.91      (((sk_D)
% 1.65/1.91         = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91            sk_D))),
% 1.65/1.91      inference('demod', [status(thm)], ['196', '209'])).
% 1.65/1.91  thf('211', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X2)
% 1.65/1.91          | ~ (v1_relat_1 @ X1)
% 1.65/1.91          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.65/1.91              = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 1.65/1.91      inference('simplify', [status(thm)], ['172'])).
% 1.65/1.91  thf('212', plain,
% 1.65/1.91      (![X15 : $i, X16 : $i]:
% 1.65/1.91         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.65/1.91          | ~ (v1_relat_1 @ X16))),
% 1.65/1.91      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.91  thf('213', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 1.65/1.91            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.91          | ~ (v1_relat_1 @ X2)
% 1.65/1.91          | ~ (v1_relat_1 @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 1.65/1.91      inference('sup+', [status(thm)], ['211', '212'])).
% 1.65/1.91  thf('214', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ sk_D)
% 1.65/1.91          | ~ (v1_relat_1 @ sk_D)
% 1.65/1.91          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.65/1.91          | ((k7_relat_1 @ 
% 1.65/1.91              (k5_relat_1 @ 
% 1.65/1.91               (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ sk_D) @ 
% 1.65/1.91              X0)
% 1.65/1.91              = (k5_relat_1 @ 
% 1.65/1.91                 (k7_relat_1 @ 
% 1.65/1.91                  (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ X0) @ 
% 1.65/1.91                 sk_D)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['210', '213'])).
% 1.65/1.91  thf('215', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.91      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.91  thf('216', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.91      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.91  thf('217', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['154', '155'])).
% 1.65/1.91  thf('218', plain,
% 1.65/1.91      (((sk_D)
% 1.65/1.91         = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91            sk_D))),
% 1.65/1.91      inference('demod', [status(thm)], ['196', '209'])).
% 1.65/1.91  thf('219', plain,
% 1.65/1.91      (((sk_D)
% 1.65/1.91         = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91            sk_D))),
% 1.65/1.91      inference('demod', [status(thm)], ['196', '209'])).
% 1.65/1.91  thf('220', plain,
% 1.65/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ X2)
% 1.65/1.91          | ~ (v1_relat_1 @ X1)
% 1.65/1.91          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.65/1.91              = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 1.65/1.91      inference('simplify', [status(thm)], ['172'])).
% 1.65/1.91  thf('221', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k5_relat_1 @ 
% 1.65/1.91            (k7_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91             X0) @ 
% 1.65/1.91            sk_D) = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))
% 1.65/1.91          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.65/1.91          | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.91      inference('sup+', [status(thm)], ['219', '220'])).
% 1.65/1.91  thf('222', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['154', '155'])).
% 1.65/1.91  thf('223', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.91      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.91  thf('224', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((k5_relat_1 @ 
% 1.65/1.91           (k7_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 1.65/1.91            X0) @ 
% 1.65/1.91           sk_D) = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 1.65/1.91      inference('demod', [status(thm)], ['221', '222', '223'])).
% 1.65/1.91  thf('225', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         ((k7_relat_1 @ sk_D @ X0) = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 1.65/1.91      inference('demod', [status(thm)],
% 1.65/1.91                ['214', '215', '216', '217', '218', '224'])).
% 1.65/1.91  thf('226', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.65/1.91      inference('demod', [status(thm)], ['85', '90'])).
% 1.65/1.91  thf('227', plain,
% 1.65/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('228', plain,
% 1.65/1.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.91         ((v4_relat_1 @ X22 @ X23)
% 1.65/1.91          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.91  thf('229', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.65/1.91      inference('sup-', [status(thm)], ['227', '228'])).
% 1.65/1.91  thf('230', plain,
% 1.65/1.91      (![X2 : $i, X3 : $i]:
% 1.65/1.91         (~ (v4_relat_1 @ X2 @ X3)
% 1.65/1.91          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 1.65/1.91          | ~ (v1_relat_1 @ X2))),
% 1.65/1.91      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.91  thf('231', plain,
% 1.65/1.91      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.65/1.91      inference('sup-', [status(thm)], ['229', '230'])).
% 1.65/1.91  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('233', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.65/1.91      inference('demod', [status(thm)], ['231', '232'])).
% 1.65/1.91  thf('234', plain,
% 1.65/1.91      (![X17 : $i]:
% 1.65/1.91         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.91          | ~ (v1_funct_1 @ X17)
% 1.65/1.91          | ~ (v1_relat_1 @ X17))),
% 1.65/1.91      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.91  thf('235', plain,
% 1.65/1.91      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.91      inference('demod', [status(thm)], ['40', '49', '50', '51', '52'])).
% 1.65/1.91  thf('236', plain,
% 1.65/1.91      (![X13 : $i, X14 : $i]:
% 1.65/1.91         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 1.65/1.91          | ((k5_relat_1 @ X13 @ (k6_partfun1 @ X14)) = (X13))
% 1.65/1.91          | ~ (v1_relat_1 @ X13))),
% 1.65/1.91      inference('demod', [status(thm)], ['140', '141'])).
% 1.65/1.91  thf('237', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 1.65/1.91          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.91          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ X0))
% 1.65/1.91              = (k2_funct_1 @ sk_C)))),
% 1.65/1.91      inference('sup-', [status(thm)], ['235', '236'])).
% 1.65/1.91  thf('238', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (~ (v1_relat_1 @ sk_C)
% 1.65/1.91          | ~ (v1_funct_1 @ sk_C)
% 1.65/1.91          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ X0))
% 1.65/1.91              = (k2_funct_1 @ sk_C))
% 1.65/1.91          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 1.65/1.91      inference('sup-', [status(thm)], ['234', '237'])).
% 1.65/1.91  thf('239', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.91      inference('demod', [status(thm)], ['46', '47'])).
% 1.65/1.91  thf('240', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('241', plain,
% 1.65/1.91      (![X0 : $i]:
% 1.65/1.91         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ X0))
% 1.65/1.91            = (k2_funct_1 @ sk_C))
% 1.65/1.91          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 1.65/1.91      inference('demod', [status(thm)], ['238', '239', '240'])).
% 1.65/1.91  thf('242', plain,
% 1.65/1.91      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.65/1.91         = (k2_funct_1 @ sk_C))),
% 1.65/1.91      inference('sup-', [status(thm)], ['233', '241'])).
% 1.65/1.91  thf('243', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.91      inference('demod', [status(thm)], ['88', '89'])).
% 1.65/1.91  thf('244', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.65/1.91      inference('demod', [status(thm)], ['80', '225', '226', '242', '243'])).
% 1.65/1.91  thf('245', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.65/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.91  thf('246', plain, ($false),
% 1.65/1.91      inference('simplify_reflect-', [status(thm)], ['244', '245'])).
% 1.65/1.91  
% 1.65/1.91  % SZS output end Refutation
% 1.65/1.91  
% 1.75/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
