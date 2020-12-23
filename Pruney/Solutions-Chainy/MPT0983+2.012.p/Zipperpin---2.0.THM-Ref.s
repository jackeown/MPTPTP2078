%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kL8NfaPQpu

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:02 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 451 expanded)
%              Number of leaves         :   39 ( 147 expanded)
%              Depth                    :   19
%              Number of atoms          : 1172 (9331 expanded)
%              Number of equality atoms :   37 ( 109 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

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

thf('4',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('26',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_partfun1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('30',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_relat_1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('39',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['36','40','43','44','45','46'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('49',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['36','40','43','44','45','46'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['50','53','54','57'])).

thf('59',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('60',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('62',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['10','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('66',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('68',plain,(
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

thf('69',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35 ) )
      | ( v2_funct_1 @ X39 )
      | ( X37 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X36 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('75',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('82',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['80','81'])).

thf('83',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['79','82'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('84',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('85',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['66','83','85','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['63','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kL8NfaPQpu
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:34:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.79/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.79/1.03  % Solved by: fo/fo7.sh
% 0.79/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.03  % done 495 iterations in 0.563s
% 0.79/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.79/1.03  % SZS output start Refutation
% 0.79/1.03  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.79/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.79/1.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.79/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.79/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.79/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/1.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.79/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/1.03  thf(sk_D_type, type, sk_D: $i).
% 0.79/1.03  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.79/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/1.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.79/1.03  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.79/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.03  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.79/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.79/1.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/1.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/1.03  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.79/1.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.79/1.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.79/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/1.03  thf(cc1_funct_1, axiom,
% 0.79/1.03    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.79/1.03  thf('0', plain, (![X5 : $i]: ((v1_funct_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.79/1.03      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.79/1.03  thf(cc2_funct_1, axiom,
% 0.79/1.03    (![A:$i]:
% 0.79/1.03     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.03       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.79/1.03  thf('1', plain,
% 0.79/1.03      (![X6 : $i]:
% 0.79/1.03         ((v2_funct_1 @ X6)
% 0.79/1.03          | ~ (v1_funct_1 @ X6)
% 0.79/1.03          | ~ (v1_relat_1 @ X6)
% 0.79/1.03          | ~ (v1_xboole_0 @ X6))),
% 0.79/1.03      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.79/1.03  thf('2', plain,
% 0.79/1.03      (![X0 : $i]:
% 0.79/1.04         (~ (v1_xboole_0 @ X0)
% 0.79/1.04          | ~ (v1_xboole_0 @ X0)
% 0.79/1.04          | ~ (v1_relat_1 @ X0)
% 0.79/1.04          | (v2_funct_1 @ X0))),
% 0.79/1.04      inference('sup-', [status(thm)], ['0', '1'])).
% 0.79/1.04  thf('3', plain,
% 0.79/1.04      (![X0 : $i]:
% 0.79/1.04         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.04      inference('simplify', [status(thm)], ['2'])).
% 0.79/1.04  thf(t29_funct_2, conjecture,
% 0.79/1.04    (![A:$i,B:$i,C:$i]:
% 0.79/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.04       ( ![D:$i]:
% 0.79/1.04         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/1.04             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/1.04           ( ( r2_relset_1 @
% 0.79/1.04               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.79/1.04               ( k6_partfun1 @ A ) ) =>
% 0.79/1.04             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.79/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.04    (~( ![A:$i,B:$i,C:$i]:
% 0.79/1.04        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.04            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.04          ( ![D:$i]:
% 0.79/1.04            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/1.04                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/1.04              ( ( r2_relset_1 @
% 0.79/1.04                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.79/1.04                  ( k6_partfun1 @ A ) ) =>
% 0.79/1.04                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.79/1.04    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.79/1.04  thf('4', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('5', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.79/1.04      inference('split', [status(esa)], ['4'])).
% 0.79/1.04  thf('6', plain,
% 0.79/1.04      (((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C)))
% 0.79/1.04         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.79/1.04      inference('sup-', [status(thm)], ['3', '5'])).
% 0.79/1.04  thf('7', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf(cc1_relset_1, axiom,
% 0.79/1.04    (![A:$i,B:$i,C:$i]:
% 0.79/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.04       ( v1_relat_1 @ C ) ))).
% 0.79/1.04  thf('8', plain,
% 0.79/1.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.79/1.04         ((v1_relat_1 @ X8)
% 0.79/1.04          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.79/1.04      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.79/1.04  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.04      inference('sup-', [status(thm)], ['7', '8'])).
% 0.79/1.04  thf('10', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.79/1.04      inference('demod', [status(thm)], ['6', '9'])).
% 0.79/1.04  thf('11', plain,
% 0.79/1.04      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.04        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/1.04        (k6_partfun1 @ sk_A))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf(redefinition_k6_partfun1, axiom,
% 0.79/1.04    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.79/1.04  thf('12', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.79/1.04      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.04  thf('13', plain,
% 0.79/1.04      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.04        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/1.04        (k6_relat_1 @ sk_A))),
% 0.79/1.04      inference('demod', [status(thm)], ['11', '12'])).
% 0.79/1.04  thf('14', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('15', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf(dt_k1_partfun1, axiom,
% 0.79/1.04    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.79/1.04     ( ( ( v1_funct_1 @ E ) & 
% 0.79/1.04         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.04         ( v1_funct_1 @ F ) & 
% 0.79/1.04         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.79/1.04       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.79/1.04         ( m1_subset_1 @
% 0.79/1.04           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.79/1.04           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.79/1.04  thf('16', plain,
% 0.79/1.04      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.79/1.04         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.79/1.04          | ~ (v1_funct_1 @ X24)
% 0.79/1.04          | ~ (v1_funct_1 @ X27)
% 0.79/1.04          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.79/1.04          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.79/1.04             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.79/1.04      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.79/1.04  thf('17', plain,
% 0.79/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.04         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/1.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/1.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/1.04          | ~ (v1_funct_1 @ X1)
% 0.79/1.04          | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.04      inference('sup-', [status(thm)], ['15', '16'])).
% 0.79/1.04  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('19', plain,
% 0.79/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.04         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/1.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/1.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/1.04          | ~ (v1_funct_1 @ X1))),
% 0.79/1.04      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/1.04  thf('20', plain,
% 0.79/1.04      ((~ (v1_funct_1 @ sk_D)
% 0.79/1.04        | (m1_subset_1 @ 
% 0.79/1.04           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/1.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/1.04      inference('sup-', [status(thm)], ['14', '19'])).
% 0.79/1.04  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('22', plain,
% 0.79/1.04      ((m1_subset_1 @ 
% 0.79/1.04        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/1.04        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.04      inference('demod', [status(thm)], ['20', '21'])).
% 0.79/1.04  thf(redefinition_r2_relset_1, axiom,
% 0.79/1.04    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.04     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.04         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.04       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.79/1.04  thf('23', plain,
% 0.79/1.04      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.79/1.04         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.79/1.04          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.79/1.04          | ((X17) = (X20))
% 0.79/1.04          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.79/1.04      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.79/1.04  thf('24', plain,
% 0.79/1.04      (![X0 : $i]:
% 0.79/1.04         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.04             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.79/1.04          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.79/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/1.04      inference('sup-', [status(thm)], ['22', '23'])).
% 0.79/1.04  thf('25', plain,
% 0.79/1.04      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.79/1.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.79/1.04        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.04            = (k6_relat_1 @ sk_A)))),
% 0.79/1.04      inference('sup-', [status(thm)], ['13', '24'])).
% 0.79/1.04  thf(t29_relset_1, axiom,
% 0.79/1.04    (![A:$i]:
% 0.79/1.04     ( m1_subset_1 @
% 0.79/1.04       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.79/1.04  thf('26', plain,
% 0.79/1.04      (![X21 : $i]:
% 0.79/1.04         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 0.79/1.04          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.79/1.04      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.79/1.04  thf('27', plain,
% 0.79/1.04      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.04         = (k6_relat_1 @ sk_A))),
% 0.79/1.04      inference('demod', [status(thm)], ['25', '26'])).
% 0.79/1.04  thf('28', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf(t24_funct_2, axiom,
% 0.79/1.04    (![A:$i,B:$i,C:$i]:
% 0.79/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.04       ( ![D:$i]:
% 0.79/1.04         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/1.04             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/1.04           ( ( r2_relset_1 @
% 0.79/1.04               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.79/1.04               ( k6_partfun1 @ B ) ) =>
% 0.79/1.04             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.79/1.04  thf('29', plain,
% 0.79/1.04      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.79/1.04         (~ (v1_funct_1 @ X31)
% 0.79/1.04          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.79/1.04          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.79/1.04          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 0.79/1.04               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 0.79/1.04               (k6_partfun1 @ X32))
% 0.79/1.04          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 0.79/1.04          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.79/1.04          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.79/1.04          | ~ (v1_funct_1 @ X34))),
% 0.79/1.04      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.79/1.04  thf('30', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.79/1.04      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.04  thf('31', plain,
% 0.79/1.04      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.79/1.04         (~ (v1_funct_1 @ X31)
% 0.79/1.04          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.79/1.04          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.79/1.04          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 0.79/1.04               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 0.79/1.04               (k6_relat_1 @ X32))
% 0.79/1.04          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 0.79/1.04          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.79/1.04          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.79/1.04          | ~ (v1_funct_1 @ X34))),
% 0.79/1.04      inference('demod', [status(thm)], ['29', '30'])).
% 0.79/1.04  thf('32', plain,
% 0.79/1.04      (![X0 : $i]:
% 0.79/1.04         (~ (v1_funct_1 @ X0)
% 0.79/1.04          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.79/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.04          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.79/1.04          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.04               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.79/1.04               (k6_relat_1 @ sk_A))
% 0.79/1.04          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.04          | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.04      inference('sup-', [status(thm)], ['28', '31'])).
% 0.79/1.04  thf('33', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('35', plain,
% 0.79/1.04      (![X0 : $i]:
% 0.79/1.04         (~ (v1_funct_1 @ X0)
% 0.79/1.04          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.79/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.04          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.79/1.04          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.04               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.79/1.04               (k6_relat_1 @ sk_A)))),
% 0.79/1.04      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.79/1.04  thf('36', plain,
% 0.79/1.04      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.79/1.04           (k6_relat_1 @ sk_A))
% 0.79/1.04        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.79/1.04        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.04        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.04        | ~ (v1_funct_1 @ sk_D))),
% 0.79/1.04      inference('sup-', [status(thm)], ['27', '35'])).
% 0.79/1.04  thf('37', plain,
% 0.79/1.04      (![X21 : $i]:
% 0.79/1.04         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 0.79/1.04          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 0.79/1.04      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.79/1.04  thf('38', plain,
% 0.79/1.04      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.79/1.04         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.79/1.04          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.79/1.04          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 0.79/1.04          | ((X17) != (X20)))),
% 0.79/1.04      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.79/1.04  thf('39', plain,
% 0.79/1.04      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/1.04         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.79/1.04          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.79/1.04      inference('simplify', [status(thm)], ['38'])).
% 0.79/1.04  thf('40', plain,
% 0.79/1.04      (![X0 : $i]:
% 0.79/1.04         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.79/1.04      inference('sup-', [status(thm)], ['37', '39'])).
% 0.79/1.04  thf('41', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf(redefinition_k2_relset_1, axiom,
% 0.79/1.04    (![A:$i,B:$i,C:$i]:
% 0.79/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.04       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.79/1.04  thf('42', plain,
% 0.79/1.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.79/1.04         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.79/1.04          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.79/1.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.79/1.04  thf('43', plain,
% 0.79/1.04      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.79/1.04      inference('sup-', [status(thm)], ['41', '42'])).
% 0.79/1.04  thf('44', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('45', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('47', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.79/1.04      inference('demod', [status(thm)], ['36', '40', '43', '44', '45', '46'])).
% 0.79/1.04  thf(d3_funct_2, axiom,
% 0.79/1.04    (![A:$i,B:$i]:
% 0.79/1.04     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.79/1.04       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.79/1.04  thf('48', plain,
% 0.79/1.04      (![X22 : $i, X23 : $i]:
% 0.79/1.04         (((k2_relat_1 @ X23) != (X22))
% 0.79/1.04          | (v2_funct_2 @ X23 @ X22)
% 0.79/1.04          | ~ (v5_relat_1 @ X23 @ X22)
% 0.79/1.04          | ~ (v1_relat_1 @ X23))),
% 0.79/1.04      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.79/1.04  thf('49', plain,
% 0.79/1.04      (![X23 : $i]:
% 0.79/1.04         (~ (v1_relat_1 @ X23)
% 0.79/1.04          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 0.79/1.04          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 0.79/1.04      inference('simplify', [status(thm)], ['48'])).
% 0.79/1.04  thf('50', plain,
% 0.79/1.04      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.79/1.04        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.79/1.04        | ~ (v1_relat_1 @ sk_D))),
% 0.79/1.04      inference('sup-', [status(thm)], ['47', '49'])).
% 0.79/1.04  thf('51', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf(cc2_relset_1, axiom,
% 0.79/1.04    (![A:$i,B:$i,C:$i]:
% 0.79/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.04       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.79/1.04  thf('52', plain,
% 0.79/1.04      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.79/1.04         ((v5_relat_1 @ X11 @ X13)
% 0.79/1.04          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.79/1.04      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/1.04  thf('53', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.79/1.04      inference('sup-', [status(thm)], ['51', '52'])).
% 0.79/1.04  thf('54', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.79/1.04      inference('demod', [status(thm)], ['36', '40', '43', '44', '45', '46'])).
% 0.79/1.04  thf('55', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('56', plain,
% 0.79/1.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.79/1.04         ((v1_relat_1 @ X8)
% 0.79/1.04          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.79/1.04      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.79/1.04  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 0.79/1.04      inference('sup-', [status(thm)], ['55', '56'])).
% 0.79/1.04  thf('58', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.79/1.04      inference('demod', [status(thm)], ['50', '53', '54', '57'])).
% 0.79/1.04  thf('59', plain,
% 0.79/1.04      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.79/1.04      inference('split', [status(esa)], ['4'])).
% 0.79/1.04  thf('60', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.79/1.04      inference('sup-', [status(thm)], ['58', '59'])).
% 0.79/1.04  thf('61', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.79/1.04      inference('split', [status(esa)], ['4'])).
% 0.79/1.04  thf('62', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.79/1.04      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.79/1.04  thf('63', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.79/1.04      inference('simpl_trail', [status(thm)], ['10', '62'])).
% 0.79/1.04  thf('64', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf(cc1_subset_1, axiom,
% 0.79/1.04    (![A:$i]:
% 0.79/1.04     ( ( v1_xboole_0 @ A ) =>
% 0.79/1.04       ( ![B:$i]:
% 0.79/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.79/1.04  thf('65', plain,
% 0.79/1.04      (![X3 : $i, X4 : $i]:
% 0.79/1.04         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.79/1.04          | (v1_xboole_0 @ X3)
% 0.79/1.04          | ~ (v1_xboole_0 @ X4))),
% 0.79/1.04      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.79/1.04  thf('66', plain,
% 0.79/1.04      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.79/1.04      inference('sup-', [status(thm)], ['64', '65'])).
% 0.79/1.04  thf('67', plain,
% 0.79/1.04      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.04         = (k6_relat_1 @ sk_A))),
% 0.79/1.04      inference('demod', [status(thm)], ['25', '26'])).
% 0.79/1.04  thf('68', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf(t26_funct_2, axiom,
% 0.79/1.04    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.04     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.79/1.04         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.04       ( ![E:$i]:
% 0.79/1.04         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.79/1.04             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.79/1.04           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.79/1.04             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.79/1.04               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.79/1.04  thf('69', plain,
% 0.79/1.04      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.79/1.04         (~ (v1_funct_1 @ X35)
% 0.79/1.04          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.79/1.04          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.79/1.04          | ~ (v2_funct_1 @ (k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35))
% 0.79/1.04          | (v2_funct_1 @ X39)
% 0.79/1.04          | ((X37) = (k1_xboole_0))
% 0.79/1.04          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 0.79/1.04          | ~ (v1_funct_2 @ X39 @ X38 @ X36)
% 0.79/1.04          | ~ (v1_funct_1 @ X39))),
% 0.79/1.04      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.79/1.04  thf('70', plain,
% 0.79/1.04      (![X0 : $i, X1 : $i]:
% 0.79/1.04         (~ (v1_funct_1 @ X0)
% 0.79/1.04          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.79/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.79/1.04          | ((sk_A) = (k1_xboole_0))
% 0.79/1.04          | (v2_funct_1 @ X0)
% 0.79/1.04          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.79/1.04          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.04          | ~ (v1_funct_1 @ sk_D))),
% 0.79/1.04      inference('sup-', [status(thm)], ['68', '69'])).
% 0.79/1.04  thf('71', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('73', plain,
% 0.79/1.04      (![X0 : $i, X1 : $i]:
% 0.79/1.04         (~ (v1_funct_1 @ X0)
% 0.79/1.04          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.79/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.79/1.04          | ((sk_A) = (k1_xboole_0))
% 0.79/1.04          | (v2_funct_1 @ X0)
% 0.79/1.04          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.79/1.04      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.79/1.04  thf('74', plain,
% 0.79/1.04      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.79/1.04        | (v2_funct_1 @ sk_C)
% 0.79/1.04        | ((sk_A) = (k1_xboole_0))
% 0.79/1.04        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.79/1.04        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.04        | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.04      inference('sup-', [status(thm)], ['67', '73'])).
% 0.79/1.04  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.79/1.04  thf('75', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.79/1.04      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.79/1.04  thf('76', plain,
% 0.79/1.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('77', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.04  thf('79', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.79/1.04      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 0.79/1.04  thf('80', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.79/1.04      inference('split', [status(esa)], ['4'])).
% 0.79/1.04  thf('81', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.79/1.04      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.79/1.04  thf('82', plain, (~ (v2_funct_1 @ sk_C)),
% 0.79/1.04      inference('simpl_trail', [status(thm)], ['80', '81'])).
% 0.79/1.04  thf('83', plain, (((sk_A) = (k1_xboole_0))),
% 0.79/1.04      inference('clc', [status(thm)], ['79', '82'])).
% 0.79/1.04  thf(t113_zfmisc_1, axiom,
% 0.79/1.04    (![A:$i,B:$i]:
% 0.79/1.04     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.79/1.04       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.79/1.04  thf('84', plain,
% 0.79/1.04      (![X1 : $i, X2 : $i]:
% 0.79/1.04         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.79/1.04      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.79/1.04  thf('85', plain,
% 0.79/1.04      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.79/1.04      inference('simplify', [status(thm)], ['84'])).
% 0.79/1.04  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.79/1.04  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.79/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.79/1.04  thf('87', plain, ((v1_xboole_0 @ sk_C)),
% 0.79/1.04      inference('demod', [status(thm)], ['66', '83', '85', '86'])).
% 0.79/1.04  thf('88', plain, ($false), inference('demod', [status(thm)], ['63', '87'])).
% 0.79/1.04  
% 0.79/1.04  % SZS output end Refutation
% 0.79/1.04  
% 0.79/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
