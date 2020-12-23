%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.axvdMd0ixP

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:04 EST 2020

% Result     : Theorem 5.35s
% Output     : Refutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 361 expanded)
%              Number of leaves         :   41 ( 126 expanded)
%              Depth                    :   14
%              Number of atoms          : 1153 (7401 expanded)
%              Number of equality atoms :   67 ( 136 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('4',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X4 ) )
      = ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('11',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('13',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('20',plain,(
    ! [X2: $i] :
      ( v1_xboole_0 @ ( sk_B @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','27'])).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('29',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_funct_2 @ X34 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('44',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('45',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
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

thf('47',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( X40
        = ( k2_funct_1 @ X43 ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40 ) @ ( k6_partfun1 @ X42 ) )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
       != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('48',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( X40
        = ( k2_funct_1 @ X43 ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40 ) @ ( k6_relat_1 @ X42 ) )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
       != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('63',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X24 )
      | ( v2_funct_2 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('64',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['64','65','66'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v2_funct_2 @ X26 @ X25 )
      | ( ( k2_relat_1 @ X26 )
        = X25 )
      | ~ ( v5_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('71',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('72',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('74',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('75',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['69','72','75'])).

thf('77',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['61','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( v3_funct_2 @ X22 @ X23 @ X24 )
      | ( v2_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('80',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','77','83'])).

thf('85',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('90',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['42','91','92'])).

thf('94',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['39','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('97',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','90'])).

thf('99',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('100',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['94','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.axvdMd0ixP
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 5.35/5.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.35/5.53  % Solved by: fo/fo7.sh
% 5.35/5.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.35/5.53  % done 6900 iterations in 5.076s
% 5.35/5.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.35/5.53  % SZS output start Refutation
% 5.35/5.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.35/5.53  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.35/5.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.35/5.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.35/5.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.35/5.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.35/5.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.35/5.53  thf(sk_A_type, type, sk_A: $i).
% 5.35/5.53  thf(sk_B_type, type, sk_B: $i > $i).
% 5.35/5.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.35/5.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.35/5.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.35/5.53  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.35/5.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.35/5.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.35/5.53  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.35/5.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.35/5.53  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 5.35/5.53  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 5.35/5.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.35/5.53  thf(sk_C_type, type, sk_C: $i).
% 5.35/5.53  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 5.35/5.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.35/5.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.35/5.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.35/5.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.35/5.53  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.35/5.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.35/5.53  thf(t8_boole, axiom,
% 5.35/5.53    (![A:$i,B:$i]:
% 5.35/5.53     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 5.35/5.53  thf('1', plain,
% 5.35/5.53      (![X0 : $i, X1 : $i]:
% 5.35/5.53         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 5.35/5.53      inference('cnf', [status(esa)], [t8_boole])).
% 5.35/5.53  thf('2', plain,
% 5.35/5.53      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.35/5.53      inference('sup-', [status(thm)], ['0', '1'])).
% 5.35/5.53  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.35/5.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.35/5.53  thf(t29_relset_1, axiom,
% 5.35/5.53    (![A:$i]:
% 5.35/5.53     ( m1_subset_1 @
% 5.35/5.53       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 5.35/5.53  thf('4', plain,
% 5.35/5.53      (![X21 : $i]:
% 5.35/5.53         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 5.35/5.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 5.35/5.53      inference('cnf', [status(esa)], [t29_relset_1])).
% 5.35/5.53  thf(cc4_relset_1, axiom,
% 5.35/5.53    (![A:$i,B:$i]:
% 5.35/5.53     ( ( v1_xboole_0 @ A ) =>
% 5.35/5.53       ( ![C:$i]:
% 5.35/5.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 5.35/5.53           ( v1_xboole_0 @ C ) ) ) ))).
% 5.35/5.53  thf('5', plain,
% 5.35/5.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.35/5.53         (~ (v1_xboole_0 @ X11)
% 5.35/5.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 5.35/5.53          | (v1_xboole_0 @ X12))),
% 5.35/5.53      inference('cnf', [status(esa)], [cc4_relset_1])).
% 5.35/5.53  thf('6', plain,
% 5.35/5.53      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 5.35/5.53      inference('sup-', [status(thm)], ['4', '5'])).
% 5.35/5.53  thf('7', plain,
% 5.35/5.53      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.35/5.53      inference('sup-', [status(thm)], ['0', '1'])).
% 5.35/5.53  thf('8', plain,
% 5.35/5.53      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_relat_1 @ X0)))),
% 5.35/5.53      inference('sup-', [status(thm)], ['6', '7'])).
% 5.35/5.53  thf('9', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 5.35/5.53      inference('sup-', [status(thm)], ['3', '8'])).
% 5.35/5.53  thf(t67_funct_1, axiom,
% 5.35/5.53    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 5.35/5.53  thf('10', plain,
% 5.35/5.53      (![X4 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X4)) = (k6_relat_1 @ X4))),
% 5.35/5.53      inference('cnf', [status(esa)], [t67_funct_1])).
% 5.35/5.53  thf('11', plain, (((k2_funct_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 5.35/5.53      inference('sup+', [status(thm)], ['9', '10'])).
% 5.35/5.53  thf('12', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 5.35/5.53      inference('sup-', [status(thm)], ['3', '8'])).
% 5.35/5.53  thf('13', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 5.35/5.53      inference('sup+', [status(thm)], ['11', '12'])).
% 5.35/5.53  thf('14', plain,
% 5.35/5.53      (![X0 : $i]: (((k1_xboole_0) = (k2_funct_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 5.35/5.53      inference('sup+', [status(thm)], ['2', '13'])).
% 5.35/5.53  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.35/5.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.35/5.53  thf('16', plain,
% 5.35/5.53      (![X0 : $i]: ((v1_xboole_0 @ (k2_funct_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 5.35/5.53      inference('sup+', [status(thm)], ['14', '15'])).
% 5.35/5.53  thf('17', plain,
% 5.35/5.53      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.35/5.53      inference('sup-', [status(thm)], ['0', '1'])).
% 5.35/5.53  thf('18', plain,
% 5.35/5.53      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.35/5.53      inference('sup-', [status(thm)], ['0', '1'])).
% 5.35/5.53  thf(rc2_subset_1, axiom,
% 5.35/5.53    (![A:$i]:
% 5.35/5.53     ( ?[B:$i]:
% 5.35/5.53       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 5.35/5.53  thf('19', plain,
% 5.35/5.53      (![X2 : $i]: (m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ X2))),
% 5.35/5.53      inference('cnf', [status(esa)], [rc2_subset_1])).
% 5.35/5.53  thf('20', plain, (![X2 : $i]: (v1_xboole_0 @ (sk_B @ X2))),
% 5.35/5.53      inference('cnf', [status(esa)], [rc2_subset_1])).
% 5.35/5.53  thf('21', plain,
% 5.35/5.53      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.35/5.53      inference('sup-', [status(thm)], ['0', '1'])).
% 5.35/5.53  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) = (sk_B @ X0))),
% 5.35/5.53      inference('sup-', [status(thm)], ['20', '21'])).
% 5.35/5.53  thf('23', plain,
% 5.35/5.53      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 5.35/5.53      inference('demod', [status(thm)], ['19', '22'])).
% 5.35/5.53  thf(redefinition_r2_relset_1, axiom,
% 5.35/5.53    (![A:$i,B:$i,C:$i,D:$i]:
% 5.35/5.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.35/5.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.35/5.53       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.35/5.53  thf('24', plain,
% 5.35/5.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 5.35/5.53         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 5.35/5.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 5.35/5.53          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 5.35/5.53          | ((X17) != (X20)))),
% 5.35/5.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.35/5.53  thf('25', plain,
% 5.35/5.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.35/5.53         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 5.35/5.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 5.35/5.53      inference('simplify', [status(thm)], ['24'])).
% 5.35/5.53  thf('26', plain,
% 5.35/5.53      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 5.35/5.53      inference('sup-', [status(thm)], ['23', '25'])).
% 5.35/5.53  thf('27', plain,
% 5.35/5.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.35/5.53         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 5.35/5.53      inference('sup+', [status(thm)], ['18', '26'])).
% 5.35/5.53  thf('28', plain,
% 5.35/5.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.35/5.53         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 5.35/5.53          | ~ (v1_xboole_0 @ X0)
% 5.35/5.53          | ~ (v1_xboole_0 @ X1))),
% 5.35/5.53      inference('sup+', [status(thm)], ['17', '27'])).
% 5.35/5.53  thf(t87_funct_2, conjecture,
% 5.35/5.53    (![A:$i,B:$i]:
% 5.35/5.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.35/5.53         ( v3_funct_2 @ B @ A @ A ) & 
% 5.35/5.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.35/5.53       ( ![C:$i]:
% 5.35/5.53         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 5.35/5.53             ( v3_funct_2 @ C @ A @ A ) & 
% 5.35/5.53             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.35/5.53           ( ( r2_relset_1 @
% 5.35/5.53               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 5.35/5.53               ( k6_partfun1 @ A ) ) =>
% 5.35/5.53             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 5.35/5.53  thf(zf_stmt_0, negated_conjecture,
% 5.35/5.53    (~( ![A:$i,B:$i]:
% 5.35/5.53        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.35/5.53            ( v3_funct_2 @ B @ A @ A ) & 
% 5.35/5.53            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.35/5.53          ( ![C:$i]:
% 5.35/5.53            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 5.35/5.53                ( v3_funct_2 @ C @ A @ A ) & 
% 5.35/5.53                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.35/5.53              ( ( r2_relset_1 @
% 5.35/5.53                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 5.35/5.53                  ( k6_partfun1 @ A ) ) =>
% 5.35/5.53                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 5.35/5.53    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 5.35/5.53  thf('29', plain,
% 5.35/5.53      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('30', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf(redefinition_k2_funct_2, axiom,
% 5.35/5.53    (![A:$i,B:$i]:
% 5.35/5.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 5.35/5.53         ( v3_funct_2 @ B @ A @ A ) & 
% 5.35/5.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 5.35/5.53       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 5.35/5.53  thf('31', plain,
% 5.35/5.53      (![X33 : $i, X34 : $i]:
% 5.35/5.53         (((k2_funct_2 @ X34 @ X33) = (k2_funct_1 @ X33))
% 5.35/5.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 5.35/5.53          | ~ (v3_funct_2 @ X33 @ X34 @ X34)
% 5.35/5.53          | ~ (v1_funct_2 @ X33 @ X34 @ X34)
% 5.35/5.53          | ~ (v1_funct_1 @ X33))),
% 5.35/5.53      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 5.35/5.53  thf('32', plain,
% 5.35/5.53      ((~ (v1_funct_1 @ sk_B_1)
% 5.35/5.53        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 5.35/5.53        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 5.35/5.53        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 5.35/5.53      inference('sup-', [status(thm)], ['30', '31'])).
% 5.35/5.53  thf('33', plain, ((v1_funct_1 @ sk_B_1)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('34', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('35', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('36', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 5.35/5.53      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 5.35/5.53  thf('37', plain,
% 5.35/5.53      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 5.35/5.53      inference('demod', [status(thm)], ['29', '36'])).
% 5.35/5.53  thf('38', plain,
% 5.35/5.53      ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B_1)))),
% 5.35/5.53      inference('sup-', [status(thm)], ['28', '37'])).
% 5.35/5.53  thf('39', plain, ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C))),
% 5.35/5.53      inference('sup-', [status(thm)], ['16', '38'])).
% 5.35/5.53  thf('40', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('41', plain,
% 5.35/5.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.35/5.53         (~ (v1_xboole_0 @ X11)
% 5.35/5.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 5.35/5.53          | (v1_xboole_0 @ X12))),
% 5.35/5.53      inference('cnf', [status(esa)], [cc4_relset_1])).
% 5.35/5.53  thf('42', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_A))),
% 5.35/5.53      inference('sup-', [status(thm)], ['40', '41'])).
% 5.35/5.53  thf('43', plain,
% 5.35/5.53      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.35/5.53        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 5.35/5.53        (k6_partfun1 @ sk_A))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf(redefinition_k6_partfun1, axiom,
% 5.35/5.53    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.35/5.53  thf('44', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 5.35/5.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.35/5.53  thf('45', plain,
% 5.35/5.53      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.35/5.53        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 5.35/5.53        (k6_relat_1 @ sk_A))),
% 5.35/5.53      inference('demod', [status(thm)], ['43', '44'])).
% 5.35/5.53  thf('46', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf(t36_funct_2, axiom,
% 5.35/5.53    (![A:$i,B:$i,C:$i]:
% 5.35/5.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.35/5.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.35/5.53       ( ![D:$i]:
% 5.35/5.53         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.35/5.53             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.35/5.53           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.35/5.53               ( r2_relset_1 @
% 5.35/5.53                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.35/5.53                 ( k6_partfun1 @ A ) ) & 
% 5.35/5.53               ( v2_funct_1 @ C ) ) =>
% 5.35/5.53             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.35/5.53               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 5.35/5.53  thf('47', plain,
% 5.35/5.53      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.35/5.53         (~ (v1_funct_1 @ X40)
% 5.35/5.53          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 5.35/5.53          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 5.35/5.53          | ((X40) = (k2_funct_1 @ X43))
% 5.35/5.53          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 5.35/5.53               (k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40) @ 
% 5.35/5.53               (k6_partfun1 @ X42))
% 5.35/5.53          | ((X41) = (k1_xboole_0))
% 5.35/5.53          | ((X42) = (k1_xboole_0))
% 5.35/5.53          | ~ (v2_funct_1 @ X43)
% 5.35/5.53          | ((k2_relset_1 @ X42 @ X41 @ X43) != (X41))
% 5.35/5.53          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 5.35/5.53          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 5.35/5.53          | ~ (v1_funct_1 @ X43))),
% 5.35/5.53      inference('cnf', [status(esa)], [t36_funct_2])).
% 5.35/5.53  thf('48', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 5.35/5.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.35/5.53  thf('49', plain,
% 5.35/5.53      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.35/5.53         (~ (v1_funct_1 @ X40)
% 5.35/5.53          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 5.35/5.53          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 5.35/5.53          | ((X40) = (k2_funct_1 @ X43))
% 5.35/5.53          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 5.35/5.53               (k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40) @ 
% 5.35/5.53               (k6_relat_1 @ X42))
% 5.35/5.53          | ((X41) = (k1_xboole_0))
% 5.35/5.53          | ((X42) = (k1_xboole_0))
% 5.35/5.53          | ~ (v2_funct_1 @ X43)
% 5.35/5.53          | ((k2_relset_1 @ X42 @ X41 @ X43) != (X41))
% 5.35/5.53          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 5.35/5.53          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 5.35/5.53          | ~ (v1_funct_1 @ X43))),
% 5.35/5.53      inference('demod', [status(thm)], ['47', '48'])).
% 5.35/5.53  thf('50', plain,
% 5.35/5.53      (![X0 : $i]:
% 5.35/5.53         (~ (v1_funct_1 @ X0)
% 5.35/5.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.35/5.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.35/5.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 5.35/5.53          | ~ (v2_funct_1 @ X0)
% 5.35/5.53          | ((sk_A) = (k1_xboole_0))
% 5.35/5.53          | ((sk_A) = (k1_xboole_0))
% 5.35/5.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.35/5.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 5.35/5.53               (k6_relat_1 @ sk_A))
% 5.35/5.53          | ((sk_C) = (k2_funct_1 @ X0))
% 5.35/5.53          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 5.35/5.53          | ~ (v1_funct_1 @ sk_C))),
% 5.35/5.53      inference('sup-', [status(thm)], ['46', '49'])).
% 5.35/5.53  thf('51', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('53', plain,
% 5.35/5.53      (![X0 : $i]:
% 5.35/5.53         (~ (v1_funct_1 @ X0)
% 5.35/5.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.35/5.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.35/5.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 5.35/5.53          | ~ (v2_funct_1 @ X0)
% 5.35/5.53          | ((sk_A) = (k1_xboole_0))
% 5.35/5.53          | ((sk_A) = (k1_xboole_0))
% 5.35/5.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.35/5.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 5.35/5.53               (k6_relat_1 @ sk_A))
% 5.35/5.53          | ((sk_C) = (k2_funct_1 @ X0)))),
% 5.35/5.53      inference('demod', [status(thm)], ['50', '51', '52'])).
% 5.35/5.53  thf('54', plain,
% 5.35/5.53      (![X0 : $i]:
% 5.35/5.53         (((sk_C) = (k2_funct_1 @ X0))
% 5.35/5.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.35/5.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 5.35/5.53               (k6_relat_1 @ sk_A))
% 5.35/5.53          | ((sk_A) = (k1_xboole_0))
% 5.35/5.53          | ~ (v2_funct_1 @ X0)
% 5.35/5.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 5.35/5.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.35/5.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 5.35/5.53          | ~ (v1_funct_1 @ X0))),
% 5.35/5.53      inference('simplify', [status(thm)], ['53'])).
% 5.35/5.53  thf('55', plain,
% 5.35/5.53      ((~ (v1_funct_1 @ sk_B_1)
% 5.35/5.53        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 5.35/5.53        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.35/5.53        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) != (sk_A))
% 5.35/5.53        | ~ (v2_funct_1 @ sk_B_1)
% 5.35/5.53        | ((sk_A) = (k1_xboole_0))
% 5.35/5.53        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 5.35/5.53      inference('sup-', [status(thm)], ['45', '54'])).
% 5.35/5.53  thf('56', plain, ((v1_funct_1 @ sk_B_1)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('57', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('58', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('59', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf(redefinition_k2_relset_1, axiom,
% 5.35/5.53    (![A:$i,B:$i,C:$i]:
% 5.35/5.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.35/5.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.35/5.53  thf('60', plain,
% 5.35/5.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.35/5.53         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 5.35/5.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 5.35/5.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.35/5.53  thf('61', plain,
% 5.35/5.53      (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k2_relat_1 @ sk_B_1))),
% 5.35/5.53      inference('sup-', [status(thm)], ['59', '60'])).
% 5.35/5.53  thf('62', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf(cc2_funct_2, axiom,
% 5.35/5.53    (![A:$i,B:$i,C:$i]:
% 5.35/5.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.35/5.53       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 5.35/5.53         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 5.35/5.53  thf('63', plain,
% 5.35/5.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.35/5.53         (~ (v1_funct_1 @ X22)
% 5.35/5.53          | ~ (v3_funct_2 @ X22 @ X23 @ X24)
% 5.35/5.53          | (v2_funct_2 @ X22 @ X24)
% 5.35/5.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 5.35/5.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 5.35/5.53  thf('64', plain,
% 5.35/5.53      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 5.35/5.53        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 5.35/5.53        | ~ (v1_funct_1 @ sk_B_1))),
% 5.35/5.53      inference('sup-', [status(thm)], ['62', '63'])).
% 5.35/5.53  thf('65', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('66', plain, ((v1_funct_1 @ sk_B_1)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('67', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 5.35/5.53      inference('demod', [status(thm)], ['64', '65', '66'])).
% 5.35/5.53  thf(d3_funct_2, axiom,
% 5.35/5.53    (![A:$i,B:$i]:
% 5.35/5.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 5.35/5.53       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 5.35/5.53  thf('68', plain,
% 5.35/5.53      (![X25 : $i, X26 : $i]:
% 5.35/5.53         (~ (v2_funct_2 @ X26 @ X25)
% 5.35/5.53          | ((k2_relat_1 @ X26) = (X25))
% 5.35/5.53          | ~ (v5_relat_1 @ X26 @ X25)
% 5.35/5.53          | ~ (v1_relat_1 @ X26))),
% 5.35/5.53      inference('cnf', [status(esa)], [d3_funct_2])).
% 5.35/5.53  thf('69', plain,
% 5.35/5.53      ((~ (v1_relat_1 @ sk_B_1)
% 5.35/5.53        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 5.35/5.53        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 5.35/5.53      inference('sup-', [status(thm)], ['67', '68'])).
% 5.35/5.53  thf('70', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf(cc1_relset_1, axiom,
% 5.35/5.53    (![A:$i,B:$i,C:$i]:
% 5.35/5.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.35/5.53       ( v1_relat_1 @ C ) ))).
% 5.35/5.53  thf('71', plain,
% 5.35/5.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 5.35/5.53         ((v1_relat_1 @ X5)
% 5.35/5.53          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 5.35/5.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.35/5.53  thf('72', plain, ((v1_relat_1 @ sk_B_1)),
% 5.35/5.53      inference('sup-', [status(thm)], ['70', '71'])).
% 5.35/5.53  thf('73', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf(cc2_relset_1, axiom,
% 5.35/5.53    (![A:$i,B:$i,C:$i]:
% 5.35/5.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.35/5.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.35/5.53  thf('74', plain,
% 5.35/5.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.35/5.53         ((v5_relat_1 @ X8 @ X10)
% 5.35/5.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 5.35/5.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.35/5.53  thf('75', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 5.35/5.53      inference('sup-', [status(thm)], ['73', '74'])).
% 5.35/5.53  thf('76', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 5.35/5.53      inference('demod', [status(thm)], ['69', '72', '75'])).
% 5.35/5.53  thf('77', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A))),
% 5.35/5.53      inference('demod', [status(thm)], ['61', '76'])).
% 5.35/5.53  thf('78', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('79', plain,
% 5.35/5.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.35/5.53         (~ (v1_funct_1 @ X22)
% 5.35/5.53          | ~ (v3_funct_2 @ X22 @ X23 @ X24)
% 5.35/5.53          | (v2_funct_1 @ X22)
% 5.35/5.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 5.35/5.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 5.35/5.53  thf('80', plain,
% 5.35/5.53      (((v2_funct_1 @ sk_B_1)
% 5.35/5.53        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 5.35/5.53        | ~ (v1_funct_1 @ sk_B_1))),
% 5.35/5.53      inference('sup-', [status(thm)], ['78', '79'])).
% 5.35/5.53  thf('81', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('82', plain, ((v1_funct_1 @ sk_B_1)),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('83', plain, ((v2_funct_1 @ sk_B_1)),
% 5.35/5.53      inference('demod', [status(thm)], ['80', '81', '82'])).
% 5.35/5.53  thf('84', plain,
% 5.35/5.53      ((((sk_A) != (sk_A))
% 5.35/5.53        | ((sk_A) = (k1_xboole_0))
% 5.35/5.53        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 5.35/5.53      inference('demod', [status(thm)], ['55', '56', '57', '58', '77', '83'])).
% 5.35/5.53  thf('85', plain,
% 5.35/5.53      ((((sk_C) = (k2_funct_1 @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 5.35/5.53      inference('simplify', [status(thm)], ['84'])).
% 5.35/5.53  thf('86', plain,
% 5.35/5.53      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 5.35/5.53      inference('demod', [status(thm)], ['29', '36'])).
% 5.35/5.53  thf('87', plain,
% 5.35/5.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 5.35/5.53      inference('sup-', [status(thm)], ['85', '86'])).
% 5.35/5.53  thf('88', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('89', plain,
% 5.35/5.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.35/5.53         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 5.35/5.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 5.35/5.53      inference('simplify', [status(thm)], ['24'])).
% 5.35/5.53  thf('90', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 5.35/5.53      inference('sup-', [status(thm)], ['88', '89'])).
% 5.35/5.53  thf('91', plain, (((sk_A) = (k1_xboole_0))),
% 5.35/5.53      inference('demod', [status(thm)], ['87', '90'])).
% 5.35/5.53  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.35/5.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.35/5.53  thf('93', plain, ((v1_xboole_0 @ sk_B_1)),
% 5.35/5.53      inference('demod', [status(thm)], ['42', '91', '92'])).
% 5.35/5.53  thf('94', plain, (~ (v1_xboole_0 @ sk_C)),
% 5.35/5.53      inference('demod', [status(thm)], ['39', '93'])).
% 5.35/5.53  thf('95', plain,
% 5.35/5.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.35/5.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.35/5.53  thf('96', plain,
% 5.35/5.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 5.35/5.53         (~ (v1_xboole_0 @ X11)
% 5.35/5.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 5.35/5.53          | (v1_xboole_0 @ X12))),
% 5.35/5.53      inference('cnf', [status(esa)], [cc4_relset_1])).
% 5.35/5.53  thf('97', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 5.35/5.53      inference('sup-', [status(thm)], ['95', '96'])).
% 5.35/5.53  thf('98', plain, (((sk_A) = (k1_xboole_0))),
% 5.35/5.53      inference('demod', [status(thm)], ['87', '90'])).
% 5.35/5.53  thf('99', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.35/5.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.35/5.53  thf('100', plain, ((v1_xboole_0 @ sk_C)),
% 5.35/5.53      inference('demod', [status(thm)], ['97', '98', '99'])).
% 5.35/5.53  thf('101', plain, ($false), inference('demod', [status(thm)], ['94', '100'])).
% 5.35/5.53  
% 5.35/5.53  % SZS output end Refutation
% 5.35/5.53  
% 5.35/5.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
