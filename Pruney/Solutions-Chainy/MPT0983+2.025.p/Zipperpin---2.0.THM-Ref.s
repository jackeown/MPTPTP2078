%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dlW95L6Qa0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:04 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 317 expanded)
%              Number of leaves         :   39 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          : 1218 (5721 expanded)
%              Number of equality atoms :   46 (  90 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('2',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('7',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('18',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf('20',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('38',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37 ) )
      | ( v2_funct_1 @ X41 )
      | ( X39 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X38 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('55',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','58','59'])).

thf('61',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['21','60'])).

thf('62',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','63'])).

thf('65',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_partfun1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('68',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_relat_1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('76',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('80',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('81',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['74','78','81','82','83','84'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('86',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('87',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('90',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['74','78','81','82','83','84'])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('94',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['88','91','92','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['64','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dlW95L6Qa0
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.81/3.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.81/3.05  % Solved by: fo/fo7.sh
% 2.81/3.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.81/3.05  % done 3592 iterations in 2.547s
% 2.81/3.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.81/3.05  % SZS output start Refutation
% 2.81/3.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.81/3.05  thf(sk_B_type, type, sk_B: $i).
% 2.81/3.05  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.81/3.05  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.81/3.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.81/3.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.81/3.05  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.81/3.05  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.81/3.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.81/3.05  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.81/3.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.81/3.05  thf(sk_C_type, type, sk_C: $i).
% 2.81/3.05  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.81/3.05  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.81/3.05  thf(sk_D_type, type, sk_D: $i).
% 2.81/3.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.81/3.05  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.81/3.05  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.81/3.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.81/3.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.81/3.05  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.81/3.05  thf(sk_A_type, type, sk_A: $i).
% 2.81/3.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.81/3.05  thf(t29_funct_2, conjecture,
% 2.81/3.05    (![A:$i,B:$i,C:$i]:
% 2.81/3.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.81/3.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.81/3.05       ( ![D:$i]:
% 2.81/3.05         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.81/3.05             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.81/3.05           ( ( r2_relset_1 @
% 2.81/3.05               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.81/3.05               ( k6_partfun1 @ A ) ) =>
% 2.81/3.05             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.81/3.05  thf(zf_stmt_0, negated_conjecture,
% 2.81/3.05    (~( ![A:$i,B:$i,C:$i]:
% 2.81/3.05        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.81/3.05            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.81/3.05          ( ![D:$i]:
% 2.81/3.05            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.81/3.05                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.81/3.05              ( ( r2_relset_1 @
% 2.81/3.05                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.81/3.05                  ( k6_partfun1 @ A ) ) =>
% 2.81/3.05                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.81/3.05    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.81/3.05  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('1', plain,
% 2.81/3.05      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.81/3.05      inference('split', [status(esa)], ['0'])).
% 2.81/3.05  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.81/3.05  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.81/3.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.81/3.05  thf(t8_boole, axiom,
% 2.81/3.05    (![A:$i,B:$i]:
% 2.81/3.05     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.81/3.05  thf('3', plain,
% 2.81/3.05      (![X0 : $i, X1 : $i]:
% 2.81/3.05         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 2.81/3.05      inference('cnf', [status(esa)], [t8_boole])).
% 2.81/3.05  thf('4', plain,
% 2.81/3.05      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.81/3.05      inference('sup-', [status(thm)], ['2', '3'])).
% 2.81/3.05  thf(t113_zfmisc_1, axiom,
% 2.81/3.05    (![A:$i,B:$i]:
% 2.81/3.05     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.81/3.05       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.81/3.05  thf('5', plain,
% 2.81/3.05      (![X3 : $i, X4 : $i]:
% 2.81/3.05         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 2.81/3.05      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.81/3.05  thf('6', plain,
% 2.81/3.05      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 2.81/3.05      inference('simplify', [status(thm)], ['5'])).
% 2.81/3.05  thf(dt_k6_partfun1, axiom,
% 2.81/3.05    (![A:$i]:
% 2.81/3.05     ( ( m1_subset_1 @
% 2.81/3.05         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.81/3.05       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.81/3.05  thf('7', plain,
% 2.81/3.05      (![X31 : $i]:
% 2.81/3.05         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 2.81/3.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.81/3.05      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.81/3.05  thf(redefinition_k6_partfun1, axiom,
% 2.81/3.05    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.81/3.05  thf('8', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.81/3.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.81/3.05  thf('9', plain,
% 2.81/3.05      (![X31 : $i]:
% 2.81/3.05         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 2.81/3.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.81/3.05      inference('demod', [status(thm)], ['7', '8'])).
% 2.81/3.05  thf('10', plain,
% 2.81/3.05      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.81/3.05      inference('sup+', [status(thm)], ['6', '9'])).
% 2.81/3.05  thf(cc1_subset_1, axiom,
% 2.81/3.05    (![A:$i]:
% 2.81/3.05     ( ( v1_xboole_0 @ A ) =>
% 2.81/3.05       ( ![B:$i]:
% 2.81/3.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 2.81/3.05  thf('11', plain,
% 2.81/3.05      (![X5 : $i, X6 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 2.81/3.05          | (v1_xboole_0 @ X5)
% 2.81/3.05          | ~ (v1_xboole_0 @ X6))),
% 2.81/3.05      inference('cnf', [status(esa)], [cc1_subset_1])).
% 2.81/3.05  thf('12', plain,
% 2.81/3.05      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.81/3.05        | (v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['10', '11'])).
% 2.81/3.05  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.81/3.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.81/3.05  thf('14', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 2.81/3.05      inference('demod', [status(thm)], ['12', '13'])).
% 2.81/3.05  thf('15', plain,
% 2.81/3.05      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.81/3.05      inference('sup-', [status(thm)], ['2', '3'])).
% 2.81/3.05  thf('16', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 2.81/3.05      inference('sup-', [status(thm)], ['14', '15'])).
% 2.81/3.05  thf(fc4_funct_1, axiom,
% 2.81/3.05    (![A:$i]:
% 2.81/3.05     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.81/3.05       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.81/3.05  thf('17', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 2.81/3.05      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.81/3.05  thf('18', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.81/3.05      inference('sup+', [status(thm)], ['16', '17'])).
% 2.81/3.05  thf('19', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.81/3.05      inference('sup+', [status(thm)], ['4', '18'])).
% 2.81/3.05  thf('20', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.81/3.05      inference('split', [status(esa)], ['0'])).
% 2.81/3.05  thf('21', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['19', '20'])).
% 2.81/3.05  thf('22', plain,
% 2.81/3.05      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.81/3.05        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.81/3.05        (k6_partfun1 @ sk_A))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('23', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.81/3.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.81/3.05  thf('24', plain,
% 2.81/3.05      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.81/3.05        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.81/3.05        (k6_relat_1 @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['22', '23'])).
% 2.81/3.05  thf('25', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('26', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf(dt_k1_partfun1, axiom,
% 2.81/3.05    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.81/3.05     ( ( ( v1_funct_1 @ E ) & 
% 2.81/3.05         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.81/3.05         ( v1_funct_1 @ F ) & 
% 2.81/3.05         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.81/3.05       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.81/3.05         ( m1_subset_1 @
% 2.81/3.05           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.81/3.05           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.81/3.05  thf('27', plain,
% 2.81/3.05      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.81/3.05          | ~ (v1_funct_1 @ X24)
% 2.81/3.05          | ~ (v1_funct_1 @ X27)
% 2.81/3.05          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.81/3.05          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 2.81/3.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 2.81/3.05      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.81/3.05  thf('28', plain,
% 2.81/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.81/3.05         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.81/3.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.81/3.05          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.81/3.05          | ~ (v1_funct_1 @ X1)
% 2.81/3.05          | ~ (v1_funct_1 @ sk_C))),
% 2.81/3.05      inference('sup-', [status(thm)], ['26', '27'])).
% 2.81/3.05  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('30', plain,
% 2.81/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.81/3.05         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.81/3.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.81/3.05          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.81/3.05          | ~ (v1_funct_1 @ X1))),
% 2.81/3.05      inference('demod', [status(thm)], ['28', '29'])).
% 2.81/3.05  thf('31', plain,
% 2.81/3.05      ((~ (v1_funct_1 @ sk_D)
% 2.81/3.05        | (m1_subset_1 @ 
% 2.81/3.05           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.81/3.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.81/3.05      inference('sup-', [status(thm)], ['25', '30'])).
% 2.81/3.05  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('33', plain,
% 2.81/3.05      ((m1_subset_1 @ 
% 2.81/3.05        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.81/3.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.81/3.05      inference('demod', [status(thm)], ['31', '32'])).
% 2.81/3.05  thf(redefinition_r2_relset_1, axiom,
% 2.81/3.05    (![A:$i,B:$i,C:$i,D:$i]:
% 2.81/3.05     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.81/3.05         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.81/3.05       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.81/3.05  thf('34', plain,
% 2.81/3.05      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.81/3.05          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.81/3.05          | ((X18) = (X21))
% 2.81/3.05          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 2.81/3.05      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.81/3.05  thf('35', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.81/3.05             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.81/3.05          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.81/3.05      inference('sup-', [status(thm)], ['33', '34'])).
% 2.81/3.05  thf('36', plain,
% 2.81/3.05      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.81/3.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.81/3.05        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.81/3.05            = (k6_relat_1 @ sk_A)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['24', '35'])).
% 2.81/3.05  thf('37', plain,
% 2.81/3.05      (![X31 : $i]:
% 2.81/3.05         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 2.81/3.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.81/3.05      inference('demod', [status(thm)], ['7', '8'])).
% 2.81/3.05  thf('38', plain,
% 2.81/3.05      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.81/3.05         = (k6_relat_1 @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['36', '37'])).
% 2.81/3.05  thf('39', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf(t26_funct_2, axiom,
% 2.81/3.05    (![A:$i,B:$i,C:$i,D:$i]:
% 2.81/3.05     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.81/3.05         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.81/3.05       ( ![E:$i]:
% 2.81/3.05         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.81/3.05             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.81/3.05           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.81/3.05             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.81/3.05               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.81/3.05  thf('40', plain,
% 2.81/3.05      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.81/3.05         (~ (v1_funct_1 @ X37)
% 2.81/3.05          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 2.81/3.05          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.81/3.05          | ~ (v2_funct_1 @ (k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37))
% 2.81/3.05          | (v2_funct_1 @ X41)
% 2.81/3.05          | ((X39) = (k1_xboole_0))
% 2.81/3.05          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X38)))
% 2.81/3.05          | ~ (v1_funct_2 @ X41 @ X40 @ X38)
% 2.81/3.05          | ~ (v1_funct_1 @ X41))),
% 2.81/3.05      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.81/3.05  thf('41', plain,
% 2.81/3.05      (![X0 : $i, X1 : $i]:
% 2.81/3.05         (~ (v1_funct_1 @ X0)
% 2.81/3.05          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.81/3.05          | ((sk_A) = (k1_xboole_0))
% 2.81/3.05          | (v2_funct_1 @ X0)
% 2.81/3.05          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.81/3.05          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.81/3.05          | ~ (v1_funct_1 @ sk_D))),
% 2.81/3.05      inference('sup-', [status(thm)], ['39', '40'])).
% 2.81/3.05  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('44', plain,
% 2.81/3.05      (![X0 : $i, X1 : $i]:
% 2.81/3.05         (~ (v1_funct_1 @ X0)
% 2.81/3.05          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.81/3.05          | ((sk_A) = (k1_xboole_0))
% 2.81/3.05          | (v2_funct_1 @ X0)
% 2.81/3.05          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.81/3.05      inference('demod', [status(thm)], ['41', '42', '43'])).
% 2.81/3.05  thf('45', plain,
% 2.81/3.05      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.81/3.05        | (v2_funct_1 @ sk_C)
% 2.81/3.05        | ((sk_A) = (k1_xboole_0))
% 2.81/3.05        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.81/3.05        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.81/3.05        | ~ (v1_funct_1 @ sk_C))),
% 2.81/3.05      inference('sup-', [status(thm)], ['38', '44'])).
% 2.81/3.05  thf('46', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 2.81/3.05      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.81/3.05  thf('47', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('48', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('50', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.81/3.05      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 2.81/3.05  thf('51', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.81/3.05      inference('split', [status(esa)], ['0'])).
% 2.81/3.05  thf('52', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['50', '51'])).
% 2.81/3.05  thf('53', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('54', plain,
% 2.81/3.05      (![X5 : $i, X6 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 2.81/3.05          | (v1_xboole_0 @ X5)
% 2.81/3.05          | ~ (v1_xboole_0 @ X6))),
% 2.81/3.05      inference('cnf', [status(esa)], [cc1_subset_1])).
% 2.81/3.05  thf('55', plain,
% 2.81/3.05      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 2.81/3.05      inference('sup-', [status(thm)], ['53', '54'])).
% 2.81/3.05  thf('56', plain,
% 2.81/3.05      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 2.81/3.05         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.81/3.05      inference('sup-', [status(thm)], ['52', '55'])).
% 2.81/3.05  thf('57', plain,
% 2.81/3.05      (![X3 : $i, X4 : $i]:
% 2.81/3.05         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.81/3.05      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.81/3.05  thf('58', plain,
% 2.81/3.05      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.81/3.05      inference('simplify', [status(thm)], ['57'])).
% 2.81/3.05  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.81/3.05      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.81/3.05  thf('60', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.81/3.05      inference('demod', [status(thm)], ['56', '58', '59'])).
% 2.81/3.05  thf('61', plain, (((v2_funct_1 @ sk_C))),
% 2.81/3.05      inference('demod', [status(thm)], ['21', '60'])).
% 2.81/3.05  thf('62', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 2.81/3.05      inference('split', [status(esa)], ['0'])).
% 2.81/3.05  thf('63', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.81/3.05      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 2.81/3.05  thf('64', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 2.81/3.05      inference('simpl_trail', [status(thm)], ['1', '63'])).
% 2.81/3.05  thf('65', plain,
% 2.81/3.05      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.81/3.05         = (k6_relat_1 @ sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['36', '37'])).
% 2.81/3.05  thf('66', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf(t24_funct_2, axiom,
% 2.81/3.05    (![A:$i,B:$i,C:$i]:
% 2.81/3.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.81/3.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.81/3.05       ( ![D:$i]:
% 2.81/3.05         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.81/3.05             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.81/3.05           ( ( r2_relset_1 @
% 2.81/3.05               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.81/3.05               ( k6_partfun1 @ B ) ) =>
% 2.81/3.05             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.81/3.05  thf('67', plain,
% 2.81/3.05      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.81/3.05         (~ (v1_funct_1 @ X33)
% 2.81/3.05          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 2.81/3.05          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.81/3.05          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 2.81/3.05               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 2.81/3.05               (k6_partfun1 @ X34))
% 2.81/3.05          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 2.81/3.05          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 2.81/3.05          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 2.81/3.05          | ~ (v1_funct_1 @ X36))),
% 2.81/3.05      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.81/3.05  thf('68', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.81/3.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.81/3.05  thf('69', plain,
% 2.81/3.05      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.81/3.05         (~ (v1_funct_1 @ X33)
% 2.81/3.05          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 2.81/3.05          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.81/3.05          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 2.81/3.05               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 2.81/3.05               (k6_relat_1 @ X34))
% 2.81/3.05          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 2.81/3.05          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 2.81/3.05          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 2.81/3.05          | ~ (v1_funct_1 @ X36))),
% 2.81/3.05      inference('demod', [status(thm)], ['67', '68'])).
% 2.81/3.05  thf('70', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         (~ (v1_funct_1 @ X0)
% 2.81/3.05          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.81/3.05          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.81/3.05          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.81/3.05               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.81/3.05               (k6_relat_1 @ sk_A))
% 2.81/3.05          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.81/3.05          | ~ (v1_funct_1 @ sk_C))),
% 2.81/3.05      inference('sup-', [status(thm)], ['66', '69'])).
% 2.81/3.05  thf('71', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('73', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         (~ (v1_funct_1 @ X0)
% 2.81/3.05          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.81/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.81/3.05          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.81/3.05          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.81/3.05               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.81/3.05               (k6_relat_1 @ sk_A)))),
% 2.81/3.05      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.81/3.05  thf('74', plain,
% 2.81/3.05      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 2.81/3.05           (k6_relat_1 @ sk_A))
% 2.81/3.05        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.81/3.05        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.81/3.05        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.81/3.05        | ~ (v1_funct_1 @ sk_D))),
% 2.81/3.05      inference('sup-', [status(thm)], ['65', '73'])).
% 2.81/3.05  thf('75', plain,
% 2.81/3.05      (![X31 : $i]:
% 2.81/3.05         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 2.81/3.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.81/3.05      inference('demod', [status(thm)], ['7', '8'])).
% 2.81/3.05  thf('76', plain,
% 2.81/3.05      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.81/3.05         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.81/3.05          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.81/3.05          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 2.81/3.05          | ((X18) != (X21)))),
% 2.81/3.05      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.81/3.05  thf('77', plain,
% 2.81/3.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.81/3.05         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 2.81/3.05          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.81/3.05      inference('simplify', [status(thm)], ['76'])).
% 2.81/3.05  thf('78', plain,
% 2.81/3.05      (![X0 : $i]:
% 2.81/3.05         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 2.81/3.05      inference('sup-', [status(thm)], ['75', '77'])).
% 2.81/3.05  thf('79', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf(redefinition_k2_relset_1, axiom,
% 2.81/3.05    (![A:$i,B:$i,C:$i]:
% 2.81/3.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.81/3.05       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.81/3.05  thf('80', plain,
% 2.81/3.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.81/3.05         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.81/3.05          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.81/3.05      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.81/3.05  thf('81', plain,
% 2.81/3.05      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.81/3.05      inference('sup-', [status(thm)], ['79', '80'])).
% 2.81/3.05  thf('82', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('83', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('84', plain, ((v1_funct_1 @ sk_D)),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf('85', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.81/3.05      inference('demod', [status(thm)], ['74', '78', '81', '82', '83', '84'])).
% 2.81/3.05  thf(d3_funct_2, axiom,
% 2.81/3.05    (![A:$i,B:$i]:
% 2.81/3.05     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.81/3.05       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.81/3.05  thf('86', plain,
% 2.81/3.05      (![X22 : $i, X23 : $i]:
% 2.81/3.05         (((k2_relat_1 @ X23) != (X22))
% 2.81/3.05          | (v2_funct_2 @ X23 @ X22)
% 2.81/3.05          | ~ (v5_relat_1 @ X23 @ X22)
% 2.81/3.05          | ~ (v1_relat_1 @ X23))),
% 2.81/3.05      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.81/3.05  thf('87', plain,
% 2.81/3.05      (![X23 : $i]:
% 2.81/3.05         (~ (v1_relat_1 @ X23)
% 2.81/3.05          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 2.81/3.05          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 2.81/3.05      inference('simplify', [status(thm)], ['86'])).
% 2.81/3.05  thf('88', plain,
% 2.81/3.05      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.81/3.05        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.81/3.05        | ~ (v1_relat_1 @ sk_D))),
% 2.81/3.05      inference('sup-', [status(thm)], ['85', '87'])).
% 2.81/3.05  thf('89', plain,
% 2.81/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.81/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.81/3.05  thf(cc2_relset_1, axiom,
% 2.81/3.05    (![A:$i,B:$i,C:$i]:
% 2.81/3.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.81/3.05       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.81/3.05  thf('90', plain,
% 2.88/3.05      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.88/3.05         ((v5_relat_1 @ X12 @ X14)
% 2.88/3.05          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.88/3.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.88/3.05  thf('91', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.88/3.05      inference('sup-', [status(thm)], ['89', '90'])).
% 2.88/3.05  thf('92', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.88/3.05      inference('demod', [status(thm)], ['74', '78', '81', '82', '83', '84'])).
% 2.88/3.05  thf('93', plain,
% 2.88/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.88/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.05  thf(cc1_relset_1, axiom,
% 2.88/3.05    (![A:$i,B:$i,C:$i]:
% 2.88/3.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.88/3.05       ( v1_relat_1 @ C ) ))).
% 2.88/3.05  thf('94', plain,
% 2.88/3.05      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.88/3.05         ((v1_relat_1 @ X9)
% 2.88/3.05          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.88/3.05      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.88/3.05  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 2.88/3.05      inference('sup-', [status(thm)], ['93', '94'])).
% 2.88/3.05  thf('96', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.88/3.05      inference('demod', [status(thm)], ['88', '91', '92', '95'])).
% 2.88/3.05  thf('97', plain, ($false), inference('demod', [status(thm)], ['64', '96'])).
% 2.88/3.05  
% 2.88/3.05  % SZS output end Refutation
% 2.88/3.05  
% 2.88/3.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
