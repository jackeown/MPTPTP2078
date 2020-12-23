%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z8FZLaU4aj

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:05 EST 2020

% Result     : Theorem 3.16s
% Output     : Refutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 317 expanded)
%              Number of leaves         :   39 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          : 1215 (5715 expanded)
%              Number of equality atoms :   46 (  90 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
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

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

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
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
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
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X42 @ X40 @ X40 @ X41 @ X43 @ X39 ) )
      | ( v2_funct_1 @ X43 )
      | ( X41 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X40 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
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
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('68',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_relat_1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
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
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('76',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ X25 )
       != X24 )
      | ( v2_funct_2 @ X25 @ X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('87',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v5_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) )
      | ( v2_funct_2 @ X25 @ ( k2_relat_1 @ X25 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z8FZLaU4aj
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.16/3.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.16/3.40  % Solved by: fo/fo7.sh
% 3.16/3.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.16/3.40  % done 5264 iterations in 2.958s
% 3.16/3.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.16/3.40  % SZS output start Refutation
% 3.16/3.40  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.16/3.40  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.16/3.40  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.16/3.40  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.16/3.40  thf(sk_B_type, type, sk_B: $i).
% 3.16/3.40  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.16/3.40  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.16/3.40  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.16/3.40  thf(sk_A_type, type, sk_A: $i).
% 3.16/3.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.16/3.40  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.16/3.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.16/3.40  thf(sk_C_type, type, sk_C: $i).
% 3.16/3.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.16/3.40  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.16/3.40  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.16/3.40  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.16/3.40  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.16/3.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.16/3.40  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.16/3.40  thf(sk_D_type, type, sk_D: $i).
% 3.16/3.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.16/3.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.16/3.40  thf(t29_funct_2, conjecture,
% 3.16/3.40    (![A:$i,B:$i,C:$i]:
% 3.16/3.40     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.16/3.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.16/3.40       ( ![D:$i]:
% 3.16/3.40         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.16/3.40             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.16/3.40           ( ( r2_relset_1 @
% 3.16/3.40               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.16/3.40               ( k6_partfun1 @ A ) ) =>
% 3.16/3.40             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.16/3.40  thf(zf_stmt_0, negated_conjecture,
% 3.16/3.40    (~( ![A:$i,B:$i,C:$i]:
% 3.16/3.40        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.16/3.40            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.16/3.40          ( ![D:$i]:
% 3.16/3.40            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.16/3.40                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.16/3.40              ( ( r2_relset_1 @
% 3.16/3.40                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.16/3.40                  ( k6_partfun1 @ A ) ) =>
% 3.16/3.40                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.16/3.40    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.16/3.40  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.16/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.40  thf('1', plain,
% 3.16/3.40      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.16/3.40      inference('split', [status(esa)], ['0'])).
% 3.16/3.40  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.16/3.40  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.16/3.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.16/3.40  thf(t8_boole, axiom,
% 3.16/3.40    (![A:$i,B:$i]:
% 3.16/3.40     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.16/3.40  thf('3', plain,
% 3.16/3.40      (![X0 : $i, X1 : $i]:
% 3.16/3.40         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.16/3.40      inference('cnf', [status(esa)], [t8_boole])).
% 3.16/3.40  thf('4', plain,
% 3.16/3.40      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.16/3.40      inference('sup-', [status(thm)], ['2', '3'])).
% 3.16/3.40  thf(t113_zfmisc_1, axiom,
% 3.16/3.40    (![A:$i,B:$i]:
% 3.16/3.40     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.16/3.40       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.16/3.40  thf('5', plain,
% 3.16/3.40      (![X3 : $i, X4 : $i]:
% 3.16/3.40         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 3.16/3.40      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.16/3.40  thf('6', plain,
% 3.16/3.40      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 3.16/3.40      inference('simplify', [status(thm)], ['5'])).
% 3.16/3.40  thf(dt_k6_partfun1, axiom,
% 3.16/3.40    (![A:$i]:
% 3.16/3.40     ( ( m1_subset_1 @
% 3.16/3.40         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.16/3.40       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.16/3.40  thf('7', plain,
% 3.16/3.40      (![X33 : $i]:
% 3.16/3.40         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 3.16/3.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 3.16/3.40      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.16/3.40  thf(redefinition_k6_partfun1, axiom,
% 3.16/3.40    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.16/3.40  thf('8', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.16/3.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.16/3.40  thf('9', plain,
% 3.16/3.40      (![X33 : $i]:
% 3.16/3.40         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 3.16/3.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 3.16/3.40      inference('demod', [status(thm)], ['7', '8'])).
% 3.16/3.40  thf('10', plain,
% 3.16/3.40      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.16/3.40      inference('sup+', [status(thm)], ['6', '9'])).
% 3.16/3.40  thf(cc1_subset_1, axiom,
% 3.16/3.40    (![A:$i]:
% 3.16/3.40     ( ( v1_xboole_0 @ A ) =>
% 3.16/3.40       ( ![B:$i]:
% 3.16/3.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.16/3.40  thf('11', plain,
% 3.16/3.40      (![X5 : $i, X6 : $i]:
% 3.16/3.40         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.16/3.40          | (v1_xboole_0 @ X5)
% 3.16/3.40          | ~ (v1_xboole_0 @ X6))),
% 3.16/3.40      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.16/3.40  thf('12', plain,
% 3.16/3.40      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.16/3.40        | (v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0)))),
% 3.16/3.40      inference('sup-', [status(thm)], ['10', '11'])).
% 3.16/3.40  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.16/3.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.16/3.40  thf('14', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 3.16/3.40      inference('demod', [status(thm)], ['12', '13'])).
% 3.16/3.40  thf('15', plain,
% 3.16/3.40      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.16/3.40      inference('sup-', [status(thm)], ['2', '3'])).
% 3.16/3.40  thf('16', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.16/3.40      inference('sup-', [status(thm)], ['14', '15'])).
% 3.16/3.40  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.16/3.40  thf('17', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 3.16/3.40      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.16/3.40  thf('18', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.16/3.40      inference('sup+', [status(thm)], ['16', '17'])).
% 3.16/3.40  thf('19', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.16/3.40      inference('sup+', [status(thm)], ['4', '18'])).
% 3.16/3.40  thf('20', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.16/3.40      inference('split', [status(esa)], ['0'])).
% 3.16/3.40  thf('21', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.16/3.40      inference('sup-', [status(thm)], ['19', '20'])).
% 3.16/3.40  thf('22', plain,
% 3.16/3.40      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.16/3.40        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.16/3.40        (k6_partfun1 @ sk_A))),
% 3.16/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.40  thf('23', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.16/3.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.16/3.40  thf('24', plain,
% 3.16/3.40      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.16/3.40        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.16/3.40        (k6_relat_1 @ sk_A))),
% 3.16/3.40      inference('demod', [status(thm)], ['22', '23'])).
% 3.16/3.40  thf('25', plain,
% 3.16/3.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.16/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.40  thf('26', plain,
% 3.16/3.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.16/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.40  thf(dt_k1_partfun1, axiom,
% 3.16/3.40    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.16/3.40     ( ( ( v1_funct_1 @ E ) & 
% 3.16/3.40         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.16/3.40         ( v1_funct_1 @ F ) & 
% 3.16/3.40         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.16/3.40       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.16/3.40         ( m1_subset_1 @
% 3.16/3.40           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.16/3.40           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.16/3.40  thf('27', plain,
% 3.16/3.40      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.16/3.40         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 3.16/3.40          | ~ (v1_funct_1 @ X26)
% 3.16/3.40          | ~ (v1_funct_1 @ X29)
% 3.16/3.40          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.16/3.40          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 3.16/3.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 3.16/3.40      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.16/3.40  thf('28', plain,
% 3.16/3.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.16/3.40         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.16/3.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.16/3.40          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.16/3.40          | ~ (v1_funct_1 @ X1)
% 3.16/3.40          | ~ (v1_funct_1 @ sk_C))),
% 3.16/3.40      inference('sup-', [status(thm)], ['26', '27'])).
% 3.16/3.40  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 3.16/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.40  thf('30', plain,
% 3.16/3.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.16/3.40         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.16/3.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.16/3.40          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.16/3.40          | ~ (v1_funct_1 @ X1))),
% 3.16/3.40      inference('demod', [status(thm)], ['28', '29'])).
% 3.16/3.40  thf('31', plain,
% 3.16/3.40      ((~ (v1_funct_1 @ sk_D)
% 3.16/3.40        | (m1_subset_1 @ 
% 3.16/3.40           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.16/3.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.16/3.40      inference('sup-', [status(thm)], ['25', '30'])).
% 3.16/3.40  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 3.16/3.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.40  thf('33', plain,
% 3.16/3.40      ((m1_subset_1 @ 
% 3.16/3.40        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.16/3.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.16/3.40      inference('demod', [status(thm)], ['31', '32'])).
% 3.16/3.40  thf(redefinition_r2_relset_1, axiom,
% 3.16/3.40    (![A:$i,B:$i,C:$i,D:$i]:
% 3.16/3.40     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.16/3.40         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.16/3.40       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.16/3.40  thf('34', plain,
% 3.16/3.40      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.16/3.40         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.16/3.40          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.16/3.40          | ((X20) = (X23))
% 3.16/3.40          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 3.16/3.40      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.16/3.40  thf('35', plain,
% 3.16/3.40      (![X0 : $i]:
% 3.16/3.40         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.16/3.40             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.16/3.40          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.16/3.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.16/3.40      inference('sup-', [status(thm)], ['33', '34'])).
% 3.16/3.40  thf('36', plain,
% 3.16/3.40      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.16/3.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.16/3.40        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.16/3.40            = (k6_relat_1 @ sk_A)))),
% 3.16/3.40      inference('sup-', [status(thm)], ['24', '35'])).
% 3.16/3.40  thf('37', plain,
% 3.16/3.40      (![X33 : $i]:
% 3.16/3.40         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 3.16/3.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 3.16/3.40      inference('demod', [status(thm)], ['7', '8'])).
% 3.16/3.40  thf('38', plain,
% 3.16/3.40      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.16/3.40         = (k6_relat_1 @ sk_A))),
% 3.16/3.41      inference('demod', [status(thm)], ['36', '37'])).
% 3.16/3.41  thf('39', plain,
% 3.16/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf(t26_funct_2, axiom,
% 3.16/3.41    (![A:$i,B:$i,C:$i,D:$i]:
% 3.16/3.41     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.16/3.41         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.16/3.41       ( ![E:$i]:
% 3.16/3.41         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.16/3.41             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.16/3.41           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.16/3.41             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.16/3.41               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.16/3.41  thf('40', plain,
% 3.16/3.41      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 3.16/3.41         (~ (v1_funct_1 @ X39)
% 3.16/3.41          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 3.16/3.41          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.16/3.41          | ~ (v2_funct_1 @ (k1_partfun1 @ X42 @ X40 @ X40 @ X41 @ X43 @ X39))
% 3.16/3.41          | (v2_funct_1 @ X43)
% 3.16/3.41          | ((X41) = (k1_xboole_0))
% 3.16/3.41          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 3.16/3.41          | ~ (v1_funct_2 @ X43 @ X42 @ X40)
% 3.16/3.41          | ~ (v1_funct_1 @ X43))),
% 3.16/3.41      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.16/3.41  thf('41', plain,
% 3.16/3.41      (![X0 : $i, X1 : $i]:
% 3.16/3.41         (~ (v1_funct_1 @ X0)
% 3.16/3.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.16/3.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.16/3.41          | ((sk_A) = (k1_xboole_0))
% 3.16/3.41          | (v2_funct_1 @ X0)
% 3.16/3.41          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.16/3.41          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.16/3.41          | ~ (v1_funct_1 @ sk_D))),
% 3.16/3.41      inference('sup-', [status(thm)], ['39', '40'])).
% 3.16/3.41  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('44', plain,
% 3.16/3.41      (![X0 : $i, X1 : $i]:
% 3.16/3.41         (~ (v1_funct_1 @ X0)
% 3.16/3.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.16/3.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.16/3.41          | ((sk_A) = (k1_xboole_0))
% 3.16/3.41          | (v2_funct_1 @ X0)
% 3.16/3.41          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.16/3.41      inference('demod', [status(thm)], ['41', '42', '43'])).
% 3.16/3.41  thf('45', plain,
% 3.16/3.41      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.16/3.41        | (v2_funct_1 @ sk_C)
% 3.16/3.41        | ((sk_A) = (k1_xboole_0))
% 3.16/3.41        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.16/3.41        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.16/3.41        | ~ (v1_funct_1 @ sk_C))),
% 3.16/3.41      inference('sup-', [status(thm)], ['38', '44'])).
% 3.16/3.41  thf('46', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 3.16/3.41      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.16/3.41  thf('47', plain,
% 3.16/3.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('48', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('50', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.16/3.41      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 3.16/3.41  thf('51', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.16/3.41      inference('split', [status(esa)], ['0'])).
% 3.16/3.41  thf('52', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.16/3.41      inference('sup-', [status(thm)], ['50', '51'])).
% 3.16/3.41  thf('53', plain,
% 3.16/3.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('54', plain,
% 3.16/3.41      (![X5 : $i, X6 : $i]:
% 3.16/3.41         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 3.16/3.41          | (v1_xboole_0 @ X5)
% 3.16/3.41          | ~ (v1_xboole_0 @ X6))),
% 3.16/3.41      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.16/3.41  thf('55', plain,
% 3.16/3.41      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.16/3.41      inference('sup-', [status(thm)], ['53', '54'])).
% 3.16/3.41  thf('56', plain,
% 3.16/3.41      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 3.16/3.41         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.16/3.41      inference('sup-', [status(thm)], ['52', '55'])).
% 3.16/3.41  thf('57', plain,
% 3.16/3.41      (![X3 : $i, X4 : $i]:
% 3.16/3.41         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 3.16/3.41      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.16/3.41  thf('58', plain,
% 3.16/3.41      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 3.16/3.41      inference('simplify', [status(thm)], ['57'])).
% 3.16/3.41  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.16/3.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.16/3.41  thf('60', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.16/3.41      inference('demod', [status(thm)], ['56', '58', '59'])).
% 3.16/3.41  thf('61', plain, (((v2_funct_1 @ sk_C))),
% 3.16/3.41      inference('demod', [status(thm)], ['21', '60'])).
% 3.16/3.41  thf('62', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 3.16/3.41      inference('split', [status(esa)], ['0'])).
% 3.16/3.41  thf('63', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.16/3.41      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 3.16/3.41  thf('64', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 3.16/3.41      inference('simpl_trail', [status(thm)], ['1', '63'])).
% 3.16/3.41  thf('65', plain,
% 3.16/3.41      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.16/3.41         = (k6_relat_1 @ sk_A))),
% 3.16/3.41      inference('demod', [status(thm)], ['36', '37'])).
% 3.16/3.41  thf('66', plain,
% 3.16/3.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf(t24_funct_2, axiom,
% 3.16/3.41    (![A:$i,B:$i,C:$i]:
% 3.16/3.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.16/3.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.16/3.41       ( ![D:$i]:
% 3.16/3.41         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.16/3.41             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.16/3.41           ( ( r2_relset_1 @
% 3.16/3.41               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.16/3.41               ( k6_partfun1 @ B ) ) =>
% 3.16/3.41             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.16/3.41  thf('67', plain,
% 3.16/3.41      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.16/3.41         (~ (v1_funct_1 @ X35)
% 3.16/3.41          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 3.16/3.41          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.16/3.41          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 3.16/3.41               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 3.16/3.41               (k6_partfun1 @ X36))
% 3.16/3.41          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 3.16/3.41          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 3.16/3.41          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 3.16/3.41          | ~ (v1_funct_1 @ X38))),
% 3.16/3.41      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.16/3.41  thf('68', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.16/3.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.16/3.41  thf('69', plain,
% 3.16/3.41      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.16/3.41         (~ (v1_funct_1 @ X35)
% 3.16/3.41          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 3.16/3.41          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.16/3.41          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 3.16/3.41               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 3.16/3.41               (k6_relat_1 @ X36))
% 3.16/3.41          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 3.16/3.41          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 3.16/3.41          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 3.16/3.41          | ~ (v1_funct_1 @ X38))),
% 3.16/3.41      inference('demod', [status(thm)], ['67', '68'])).
% 3.16/3.41  thf('70', plain,
% 3.16/3.41      (![X0 : $i]:
% 3.16/3.41         (~ (v1_funct_1 @ X0)
% 3.16/3.41          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.16/3.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.16/3.41          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.16/3.41          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.16/3.41               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.16/3.41               (k6_relat_1 @ sk_A))
% 3.16/3.41          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.16/3.41          | ~ (v1_funct_1 @ sk_C))),
% 3.16/3.41      inference('sup-', [status(thm)], ['66', '69'])).
% 3.16/3.41  thf('71', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('73', plain,
% 3.16/3.41      (![X0 : $i]:
% 3.16/3.41         (~ (v1_funct_1 @ X0)
% 3.16/3.41          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.16/3.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.16/3.41          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.16/3.41          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.16/3.41               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.16/3.41               (k6_relat_1 @ sk_A)))),
% 3.16/3.41      inference('demod', [status(thm)], ['70', '71', '72'])).
% 3.16/3.41  thf('74', plain,
% 3.16/3.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 3.16/3.41           (k6_relat_1 @ sk_A))
% 3.16/3.41        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.16/3.41        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.16/3.41        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.16/3.41        | ~ (v1_funct_1 @ sk_D))),
% 3.16/3.41      inference('sup-', [status(thm)], ['65', '73'])).
% 3.16/3.41  thf('75', plain,
% 3.16/3.41      (![X33 : $i]:
% 3.16/3.41         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 3.16/3.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 3.16/3.41      inference('demod', [status(thm)], ['7', '8'])).
% 3.16/3.41  thf('76', plain,
% 3.16/3.41      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.16/3.41         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.16/3.41          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.16/3.41          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 3.16/3.41          | ((X20) != (X23)))),
% 3.16/3.41      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.16/3.41  thf('77', plain,
% 3.16/3.41      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.16/3.41         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 3.16/3.41          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.16/3.41      inference('simplify', [status(thm)], ['76'])).
% 3.16/3.41  thf('78', plain,
% 3.16/3.41      (![X0 : $i]:
% 3.16/3.41         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.16/3.41      inference('sup-', [status(thm)], ['75', '77'])).
% 3.16/3.41  thf('79', plain,
% 3.16/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf(redefinition_k2_relset_1, axiom,
% 3.16/3.41    (![A:$i,B:$i,C:$i]:
% 3.16/3.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.16/3.41       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.16/3.41  thf('80', plain,
% 3.16/3.41      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.16/3.41         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 3.16/3.41          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.16/3.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.16/3.41  thf('81', plain,
% 3.16/3.41      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.16/3.41      inference('sup-', [status(thm)], ['79', '80'])).
% 3.16/3.41  thf('82', plain,
% 3.16/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('83', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('84', plain, ((v1_funct_1 @ sk_D)),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf('85', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.16/3.41      inference('demod', [status(thm)], ['74', '78', '81', '82', '83', '84'])).
% 3.16/3.41  thf(d3_funct_2, axiom,
% 3.16/3.41    (![A:$i,B:$i]:
% 3.16/3.41     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.16/3.41       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.16/3.41  thf('86', plain,
% 3.16/3.41      (![X24 : $i, X25 : $i]:
% 3.16/3.41         (((k2_relat_1 @ X25) != (X24))
% 3.16/3.41          | (v2_funct_2 @ X25 @ X24)
% 3.16/3.41          | ~ (v5_relat_1 @ X25 @ X24)
% 3.16/3.41          | ~ (v1_relat_1 @ X25))),
% 3.16/3.41      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.16/3.41  thf('87', plain,
% 3.16/3.41      (![X25 : $i]:
% 3.16/3.41         (~ (v1_relat_1 @ X25)
% 3.16/3.41          | ~ (v5_relat_1 @ X25 @ (k2_relat_1 @ X25))
% 3.16/3.41          | (v2_funct_2 @ X25 @ (k2_relat_1 @ X25)))),
% 3.16/3.41      inference('simplify', [status(thm)], ['86'])).
% 3.16/3.41  thf('88', plain,
% 3.16/3.41      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.16/3.41        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.16/3.41        | ~ (v1_relat_1 @ sk_D))),
% 3.16/3.41      inference('sup-', [status(thm)], ['85', '87'])).
% 3.16/3.41  thf('89', plain,
% 3.16/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf(cc2_relset_1, axiom,
% 3.16/3.41    (![A:$i,B:$i,C:$i]:
% 3.16/3.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.16/3.41       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.16/3.41  thf('90', plain,
% 3.16/3.41      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.16/3.41         ((v5_relat_1 @ X14 @ X16)
% 3.16/3.41          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.16/3.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.16/3.41  thf('91', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.16/3.41      inference('sup-', [status(thm)], ['89', '90'])).
% 3.16/3.41  thf('92', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.16/3.41      inference('demod', [status(thm)], ['74', '78', '81', '82', '83', '84'])).
% 3.16/3.41  thf('93', plain,
% 3.16/3.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.16/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.16/3.41  thf(cc1_relset_1, axiom,
% 3.16/3.41    (![A:$i,B:$i,C:$i]:
% 3.16/3.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.16/3.41       ( v1_relat_1 @ C ) ))).
% 3.16/3.41  thf('94', plain,
% 3.16/3.41      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.16/3.41         ((v1_relat_1 @ X11)
% 3.16/3.41          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 3.16/3.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.16/3.41  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 3.16/3.41      inference('sup-', [status(thm)], ['93', '94'])).
% 3.16/3.41  thf('96', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.16/3.41      inference('demod', [status(thm)], ['88', '91', '92', '95'])).
% 3.16/3.41  thf('97', plain, ($false), inference('demod', [status(thm)], ['64', '96'])).
% 3.16/3.41  
% 3.16/3.41  % SZS output end Refutation
% 3.16/3.41  
% 3.16/3.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
