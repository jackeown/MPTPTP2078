%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QO2DDsWzY6

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:02 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 479 expanded)
%              Number of leaves         :   40 ( 157 expanded)
%              Depth                    :   19
%              Number of atoms          : 1188 (9520 expanded)
%              Number of equality atoms :   38 ( 127 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
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

thf('31',plain,(
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

thf('32',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_relat_1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','42','45','46','47','48'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != X21 )
      | ( v2_funct_2 @ X22 @ X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('51',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
      | ( v2_funct_2 @ X22 @ ( k2_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','42','45','46','47','48'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['52','55','56','59'])).

thf('61',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('62',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('64',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['10','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('70',plain,(
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

thf('71',plain,(
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

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('77',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('83',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('84',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['81','84'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('86',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('87',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['68','85','87','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['65','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QO2DDsWzY6
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.76  % Solved by: fo/fo7.sh
% 0.53/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.76  % done 497 iterations in 0.301s
% 0.53/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.76  % SZS output start Refutation
% 0.53/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.53/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.76  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.53/0.76  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.53/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.76  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.53/0.76  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.53/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.53/0.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.53/0.76  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.53/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.53/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.76  thf(cc1_funct_1, axiom,
% 0.53/0.76    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.53/0.76  thf('0', plain, (![X5 : $i]: ((v1_funct_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.53/0.76      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.53/0.76  thf(cc2_funct_1, axiom,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.53/0.76       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.53/0.76  thf('1', plain,
% 0.53/0.76      (![X6 : $i]:
% 0.53/0.76         ((v2_funct_1 @ X6)
% 0.53/0.76          | ~ (v1_funct_1 @ X6)
% 0.53/0.76          | ~ (v1_relat_1 @ X6)
% 0.53/0.76          | ~ (v1_xboole_0 @ X6))),
% 0.53/0.76      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.53/0.76  thf('2', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         (~ (v1_xboole_0 @ X0)
% 0.53/0.76          | ~ (v1_xboole_0 @ X0)
% 0.53/0.76          | ~ (v1_relat_1 @ X0)
% 0.53/0.76          | (v2_funct_1 @ X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.76  thf('3', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.76      inference('simplify', [status(thm)], ['2'])).
% 0.53/0.76  thf(t29_funct_2, conjecture,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.76       ( ![D:$i]:
% 0.53/0.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.76           ( ( r2_relset_1 @
% 0.53/0.76               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.53/0.76               ( k6_partfun1 @ A ) ) =>
% 0.53/0.76             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.53/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.76        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.76            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.76          ( ![D:$i]:
% 0.53/0.76            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.76                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.76              ( ( r2_relset_1 @
% 0.53/0.76                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.53/0.76                  ( k6_partfun1 @ A ) ) =>
% 0.53/0.76                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.53/0.76    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.53/0.76  thf('4', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('5', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.76      inference('split', [status(esa)], ['4'])).
% 0.53/0.76  thf('6', plain,
% 0.53/0.76      (((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C)))
% 0.53/0.76         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['3', '5'])).
% 0.53/0.76  thf('7', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(cc1_relset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.76       ( v1_relat_1 @ C ) ))).
% 0.53/0.76  thf('8', plain,
% 0.53/0.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.53/0.76         ((v1_relat_1 @ X8)
% 0.53/0.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.53/0.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.53/0.76  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.76  thf('10', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.76      inference('demod', [status(thm)], ['6', '9'])).
% 0.53/0.76  thf('11', plain,
% 0.53/0.76      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.76        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.76        (k6_partfun1 @ sk_A))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(redefinition_k6_partfun1, axiom,
% 0.53/0.76    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.53/0.76  thf('12', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.53/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.76  thf('13', plain,
% 0.53/0.76      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.76        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.76        (k6_relat_1 @ sk_A))),
% 0.53/0.76      inference('demod', [status(thm)], ['11', '12'])).
% 0.53/0.76  thf('14', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('15', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(dt_k1_partfun1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.76     ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.76         ( v1_funct_1 @ F ) & 
% 0.53/0.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.53/0.76       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.53/0.76         ( m1_subset_1 @
% 0.53/0.76           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.53/0.76           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.53/0.76  thf('16', plain,
% 0.53/0.76      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.53/0.76          | ~ (v1_funct_1 @ X23)
% 0.53/0.76          | ~ (v1_funct_1 @ X26)
% 0.53/0.76          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.53/0.76          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 0.53/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 0.53/0.76      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.53/0.76  thf('17', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.53/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.53/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.53/0.76          | ~ (v1_funct_1 @ X1)
% 0.53/0.76          | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.53/0.76  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('19', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.53/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.53/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.53/0.76          | ~ (v1_funct_1 @ X1))),
% 0.53/0.76      inference('demod', [status(thm)], ['17', '18'])).
% 0.53/0.76  thf('20', plain,
% 0.53/0.76      ((~ (v1_funct_1 @ sk_D)
% 0.53/0.76        | (m1_subset_1 @ 
% 0.53/0.76           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['14', '19'])).
% 0.53/0.76  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('22', plain,
% 0.53/0.76      ((m1_subset_1 @ 
% 0.53/0.76        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.53/0.76      inference('demod', [status(thm)], ['20', '21'])).
% 0.53/0.76  thf(redefinition_r2_relset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.76       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.53/0.76  thf('23', plain,
% 0.53/0.76      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.53/0.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.53/0.76          | ((X17) = (X20))
% 0.53/0.76          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.53/0.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.53/0.76  thf('24', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.76             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.53/0.76          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.53/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.76  thf('25', plain,
% 0.53/0.76      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.53/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.53/0.76        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.76            = (k6_relat_1 @ sk_A)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['13', '24'])).
% 0.53/0.76  thf(dt_k6_partfun1, axiom,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( m1_subset_1 @
% 0.53/0.76         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.53/0.76       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.53/0.76  thf('26', plain,
% 0.53/0.76      (![X30 : $i]:
% 0.53/0.76         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 0.53/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.53/0.76      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.53/0.76  thf('27', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.53/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.76  thf('28', plain,
% 0.53/0.76      (![X30 : $i]:
% 0.53/0.76         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 0.53/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.53/0.76      inference('demod', [status(thm)], ['26', '27'])).
% 0.53/0.76  thf('29', plain,
% 0.53/0.76      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.76         = (k6_relat_1 @ sk_A))),
% 0.53/0.76      inference('demod', [status(thm)], ['25', '28'])).
% 0.53/0.76  thf('30', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(t24_funct_2, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.76       ( ![D:$i]:
% 0.53/0.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.76           ( ( r2_relset_1 @
% 0.53/0.76               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.53/0.76               ( k6_partfun1 @ B ) ) =>
% 0.53/0.76             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.53/0.76  thf('31', plain,
% 0.53/0.76      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.53/0.76         (~ (v1_funct_1 @ X32)
% 0.53/0.76          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.53/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.53/0.76          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 0.53/0.76               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 0.53/0.76               (k6_partfun1 @ X33))
% 0.53/0.76          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 0.53/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.53/0.76          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.53/0.76          | ~ (v1_funct_1 @ X35))),
% 0.53/0.76      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.53/0.76  thf('32', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.53/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.76  thf('33', plain,
% 0.53/0.76      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.53/0.76         (~ (v1_funct_1 @ X32)
% 0.53/0.76          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.53/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.53/0.76          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 0.53/0.76               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 0.53/0.76               (k6_relat_1 @ X33))
% 0.53/0.76          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 0.53/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.53/0.76          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.53/0.76          | ~ (v1_funct_1 @ X35))),
% 0.53/0.76      inference('demod', [status(thm)], ['31', '32'])).
% 0.53/0.76  thf('34', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         (~ (v1_funct_1 @ X0)
% 0.53/0.76          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.53/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.76          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.53/0.76          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.76               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.53/0.76               (k6_relat_1 @ sk_A))
% 0.53/0.76          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.53/0.76          | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.76      inference('sup-', [status(thm)], ['30', '33'])).
% 0.53/0.76  thf('35', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('37', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         (~ (v1_funct_1 @ X0)
% 0.53/0.76          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.53/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.76          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.53/0.76          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.76               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.53/0.76               (k6_relat_1 @ sk_A)))),
% 0.53/0.76      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.53/0.76  thf('38', plain,
% 0.53/0.76      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.53/0.76           (k6_relat_1 @ sk_A))
% 0.53/0.76        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.53/0.76        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.76        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.53/0.76        | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.76      inference('sup-', [status(thm)], ['29', '37'])).
% 0.53/0.76  thf('39', plain,
% 0.53/0.76      (![X30 : $i]:
% 0.53/0.76         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 0.53/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.53/0.76      inference('demod', [status(thm)], ['26', '27'])).
% 0.53/0.76  thf('40', plain,
% 0.53/0.76      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.53/0.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.53/0.76          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 0.53/0.76          | ((X17) != (X20)))),
% 0.53/0.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.53/0.76  thf('41', plain,
% 0.53/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.76         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 0.53/0.76          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.53/0.76      inference('simplify', [status(thm)], ['40'])).
% 0.53/0.76  thf('42', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.53/0.76      inference('sup-', [status(thm)], ['39', '41'])).
% 0.53/0.76  thf('43', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(redefinition_k2_relset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.53/0.76  thf('44', plain,
% 0.53/0.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.76         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.53/0.76          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.53/0.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.53/0.76  thf('45', plain,
% 0.53/0.76      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.53/0.76      inference('sup-', [status(thm)], ['43', '44'])).
% 0.53/0.76  thf('46', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.53/0.76      inference('demod', [status(thm)], ['38', '42', '45', '46', '47', '48'])).
% 0.53/0.76  thf(d3_funct_2, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.53/0.76       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.53/0.76  thf('50', plain,
% 0.53/0.76      (![X21 : $i, X22 : $i]:
% 0.53/0.76         (((k2_relat_1 @ X22) != (X21))
% 0.53/0.76          | (v2_funct_2 @ X22 @ X21)
% 0.53/0.76          | ~ (v5_relat_1 @ X22 @ X21)
% 0.53/0.76          | ~ (v1_relat_1 @ X22))),
% 0.53/0.76      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.53/0.76  thf('51', plain,
% 0.53/0.76      (![X22 : $i]:
% 0.53/0.76         (~ (v1_relat_1 @ X22)
% 0.53/0.76          | ~ (v5_relat_1 @ X22 @ (k2_relat_1 @ X22))
% 0.53/0.76          | (v2_funct_2 @ X22 @ (k2_relat_1 @ X22)))),
% 0.53/0.76      inference('simplify', [status(thm)], ['50'])).
% 0.53/0.76  thf('52', plain,
% 0.53/0.76      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.53/0.76        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.53/0.76        | ~ (v1_relat_1 @ sk_D))),
% 0.53/0.76      inference('sup-', [status(thm)], ['49', '51'])).
% 0.53/0.76  thf('53', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(cc2_relset_1, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.53/0.76  thf('54', plain,
% 0.53/0.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.76         ((v5_relat_1 @ X11 @ X13)
% 0.53/0.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.53/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.53/0.76  thf('55', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.53/0.76      inference('sup-', [status(thm)], ['53', '54'])).
% 0.53/0.76  thf('56', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.53/0.76      inference('demod', [status(thm)], ['38', '42', '45', '46', '47', '48'])).
% 0.53/0.76  thf('57', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('58', plain,
% 0.53/0.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.53/0.76         ((v1_relat_1 @ X8)
% 0.53/0.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.53/0.76      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.53/0.76  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.76      inference('sup-', [status(thm)], ['57', '58'])).
% 0.53/0.76  thf('60', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.53/0.76      inference('demod', [status(thm)], ['52', '55', '56', '59'])).
% 0.53/0.76  thf('61', plain,
% 0.53/0.76      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.53/0.76      inference('split', [status(esa)], ['4'])).
% 0.53/0.76  thf('62', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.76      inference('sup-', [status(thm)], ['60', '61'])).
% 0.53/0.76  thf('63', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.76      inference('split', [status(esa)], ['4'])).
% 0.53/0.76  thf('64', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.53/0.76      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.53/0.76  thf('65', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.53/0.76      inference('simpl_trail', [status(thm)], ['10', '64'])).
% 0.53/0.76  thf('66', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(cc1_subset_1, axiom,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( v1_xboole_0 @ A ) =>
% 0.53/0.76       ( ![B:$i]:
% 0.53/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.53/0.76  thf('67', plain,
% 0.53/0.76      (![X3 : $i, X4 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.53/0.76          | (v1_xboole_0 @ X3)
% 0.53/0.76          | ~ (v1_xboole_0 @ X4))),
% 0.53/0.76      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.53/0.76  thf('68', plain,
% 0.53/0.76      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.53/0.76      inference('sup-', [status(thm)], ['66', '67'])).
% 0.53/0.76  thf('69', plain,
% 0.53/0.76      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.76         = (k6_relat_1 @ sk_A))),
% 0.53/0.76      inference('demod', [status(thm)], ['25', '28'])).
% 0.53/0.76  thf('70', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(t26_funct_2, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.76       ( ![E:$i]:
% 0.53/0.76         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.53/0.76             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.53/0.76           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.53/0.76             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.53/0.76               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.53/0.76  thf('71', plain,
% 0.53/0.76      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.53/0.76         (~ (v1_funct_1 @ X36)
% 0.53/0.76          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.53/0.76          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.53/0.76          | ~ (v2_funct_1 @ (k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36))
% 0.53/0.76          | (v2_funct_1 @ X40)
% 0.53/0.76          | ((X38) = (k1_xboole_0))
% 0.53/0.76          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.53/0.76          | ~ (v1_funct_2 @ X40 @ X39 @ X37)
% 0.53/0.76          | ~ (v1_funct_1 @ X40))),
% 0.53/0.76      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.53/0.76  thf('72', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (~ (v1_funct_1 @ X0)
% 0.53/0.76          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.53/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.53/0.76          | ((sk_A) = (k1_xboole_0))
% 0.53/0.76          | (v2_funct_1 @ X0)
% 0.53/0.76          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.53/0.76          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.53/0.76          | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.76      inference('sup-', [status(thm)], ['70', '71'])).
% 0.53/0.76  thf('73', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('75', plain,
% 0.53/0.76      (![X0 : $i, X1 : $i]:
% 0.53/0.76         (~ (v1_funct_1 @ X0)
% 0.53/0.76          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.53/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.53/0.76          | ((sk_A) = (k1_xboole_0))
% 0.53/0.76          | (v2_funct_1 @ X0)
% 0.53/0.76          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.53/0.76      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.53/0.76  thf('76', plain,
% 0.53/0.76      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.53/0.76        | (v2_funct_1 @ sk_C)
% 0.53/0.76        | ((sk_A) = (k1_xboole_0))
% 0.53/0.76        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.53/0.76        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.53/0.76        | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.76      inference('sup-', [status(thm)], ['69', '75'])).
% 0.53/0.76  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.53/0.76  thf('77', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.53/0.76      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.53/0.76  thf('78', plain,
% 0.53/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('79', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('81', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.76      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.53/0.76  thf('82', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.76      inference('split', [status(esa)], ['4'])).
% 0.53/0.76  thf('83', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.53/0.76      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.53/0.76  thf('84', plain, (~ (v2_funct_1 @ sk_C)),
% 0.53/0.76      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.53/0.76  thf('85', plain, (((sk_A) = (k1_xboole_0))),
% 0.53/0.76      inference('clc', [status(thm)], ['81', '84'])).
% 0.53/0.76  thf(t113_zfmisc_1, axiom,
% 0.53/0.76    (![A:$i,B:$i]:
% 0.53/0.76     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.53/0.76       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.53/0.76  thf('86', plain,
% 0.53/0.76      (![X1 : $i, X2 : $i]:
% 0.53/0.76         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.53/0.76      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.53/0.76  thf('87', plain,
% 0.53/0.76      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.53/0.76      inference('simplify', [status(thm)], ['86'])).
% 0.53/0.76  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.53/0.76  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.76  thf('89', plain, ((v1_xboole_0 @ sk_C)),
% 0.53/0.76      inference('demod', [status(thm)], ['68', '85', '87', '88'])).
% 0.53/0.76  thf('90', plain, ($false), inference('demod', [status(thm)], ['65', '89'])).
% 0.53/0.76  
% 0.53/0.76  % SZS output end Refutation
% 0.53/0.76  
% 0.53/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
