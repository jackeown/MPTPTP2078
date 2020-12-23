%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AAk25PWU36

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:34 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  247 (1444 expanded)
%              Number of leaves         :   56 ( 473 expanded)
%              Depth                    :   31
%              Number of atoms          : 1899 (17386 expanded)
%              Number of equality atoms :  112 ( 848 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t31_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
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

thf('20',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['20','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('42',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf(t9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('45',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ X46 @ X47 )
      | ( zip_tseitin_1 @ X46 @ X48 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ( zip_tseitin_0 @ X49 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B_1 )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['23','24'])).

thf('48',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('49',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('50',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('51',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('52',plain,(
    ! [X40: $i] :
      ( ( v1_funct_2 @ X40 @ ( k1_relat_1 @ X40 ) @ ( k2_relat_1 @ X40 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['47','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['46','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B_1 )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','69'])).

thf('71',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_funct_2 @ X41 @ X43 @ X42 )
      | ~ ( zip_tseitin_0 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('72',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('77',plain,(
    ! [X12: $i] :
      ( ( ( k1_relat_1 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('78',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('80',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('82',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('83',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('84',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('85',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('86',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('88',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('89',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('90',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_partfun1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('92',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('93',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X18 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','94'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('96',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
        = ( k2_funct_1 @ X24 ) )
      | ( ( k5_relat_1 @ X24 @ X23 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X24 ) ) )
      | ( ( k2_relat_1 @ X24 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('97',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('98',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
        = ( k2_funct_1 @ X24 ) )
      | ( ( k5_relat_1 @ X24 @ X23 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X24 ) ) )
      | ( ( k2_relat_1 @ X24 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k6_partfun1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('101',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('102',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X18 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('104',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('105',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('106',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('108',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_partfun1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('109',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X21 @ X20 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X21 ) ) )
      | ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('110',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X21 @ X20 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X21 ) ) )
      | ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('114',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X18 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X18 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('119',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('123',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('124',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('125',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X18 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ( X0 != X0 )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['99','102','103','106','121','122','123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','127'])).

thf('129',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('130',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','81','130'])).

thf('132',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('133',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X13 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('134',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['23','24'])).

thf('137',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('140',plain,(
    ! [X37: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X37 ) @ X37 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('141',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['139','140'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('142',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('146',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('147',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('151',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X18 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('152',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['149','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','153'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('155',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['150','151'])).

thf('160',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['145','146'])).

thf('161',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('162',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('163',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('164',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_partfun1 @ X34 @ X35 )
      | ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('167',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('168',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['165','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['141','169'])).

thf('171',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['131','138','170'])).

thf('172',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('173',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','171','172'])).

thf('174',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','173'])).

thf('175',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B_1 )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','69'])).

thf('176',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( zip_tseitin_0 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('177',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','173'])).

thf('179',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X44: $i,X45: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X12: $i] :
      ( ( ( k1_relat_1 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('183',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('185',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('188',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('189',plain,(
    $false ),
    inference(demod,[status(thm)],['174','186','187','188'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AAk25PWU36
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:20:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.80/2.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.80/2.00  % Solved by: fo/fo7.sh
% 1.80/2.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/2.00  % done 2665 iterations in 1.538s
% 1.80/2.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.80/2.00  % SZS output start Refutation
% 1.80/2.00  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.80/2.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 1.80/2.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.80/2.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.80/2.00  thf(sk_A_type, type, sk_A: $i).
% 1.80/2.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.80/2.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.80/2.00  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.80/2.00  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.80/2.00  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.80/2.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.80/2.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.80/2.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.80/2.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.80/2.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.80/2.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.80/2.00  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.80/2.00  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.80/2.00  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.80/2.00  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.80/2.00  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.80/2.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.80/2.00  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.80/2.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.80/2.00  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.80/2.00  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.80/2.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.80/2.00  thf(t31_funct_2, conjecture,
% 1.80/2.00    (![A:$i,B:$i,C:$i]:
% 1.80/2.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.80/2.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.80/2.00       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.80/2.00         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.80/2.00           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.80/2.00           ( m1_subset_1 @
% 1.80/2.00             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.80/2.00  thf(zf_stmt_0, negated_conjecture,
% 1.80/2.00    (~( ![A:$i,B:$i,C:$i]:
% 1.80/2.00        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.80/2.00            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.80/2.00          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.80/2.00            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.80/2.00              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.80/2.00              ( m1_subset_1 @
% 1.80/2.00                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.80/2.00    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.80/2.00  thf('0', plain,
% 1.80/2.00      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.80/2.00        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 1.80/2.00        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf('1', plain,
% 1.80/2.00      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 1.80/2.00         <= (~
% 1.80/2.00             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.80/2.00      inference('split', [status(esa)], ['0'])).
% 1.80/2.00  thf('2', plain,
% 1.80/2.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf(cc1_relset_1, axiom,
% 1.80/2.00    (![A:$i,B:$i,C:$i]:
% 1.80/2.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.80/2.00       ( v1_relat_1 @ C ) ))).
% 1.80/2.00  thf('3', plain,
% 1.80/2.00      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.80/2.00         ((v1_relat_1 @ X25)
% 1.80/2.00          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.80/2.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.80/2.00  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 1.80/2.00      inference('sup-', [status(thm)], ['2', '3'])).
% 1.80/2.00  thf(dt_k2_funct_1, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.80/2.00       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.80/2.00         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.80/2.00  thf('5', plain,
% 1.80/2.00      (![X17 : $i]:
% 1.80/2.00         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 1.80/2.00          | ~ (v1_funct_1 @ X17)
% 1.80/2.00          | ~ (v1_relat_1 @ X17))),
% 1.80/2.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.80/2.00  thf('6', plain,
% 1.80/2.00      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.80/2.00         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.80/2.00      inference('split', [status(esa)], ['0'])).
% 1.80/2.00  thf('7', plain,
% 1.80/2.00      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 1.80/2.00         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.80/2.00      inference('sup-', [status(thm)], ['5', '6'])).
% 1.80/2.00  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf('9', plain,
% 1.80/2.00      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.80/2.00      inference('demod', [status(thm)], ['7', '8'])).
% 1.80/2.00  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.80/2.00      inference('sup-', [status(thm)], ['4', '9'])).
% 1.80/2.00  thf('11', plain,
% 1.80/2.00      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('split', [status(esa)], ['0'])).
% 1.80/2.00  thf('12', plain,
% 1.80/2.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf(cc2_relset_1, axiom,
% 1.80/2.00    (![A:$i,B:$i,C:$i]:
% 1.80/2.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.80/2.00       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.80/2.00  thf('13', plain,
% 1.80/2.00      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.80/2.00         ((v4_relat_1 @ X28 @ X29)
% 1.80/2.00          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.80/2.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.80/2.00  thf('14', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 1.80/2.00      inference('sup-', [status(thm)], ['12', '13'])).
% 1.80/2.00  thf(d18_relat_1, axiom,
% 1.80/2.00    (![A:$i,B:$i]:
% 1.80/2.00     ( ( v1_relat_1 @ B ) =>
% 1.80/2.00       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.80/2.00  thf('15', plain,
% 1.80/2.00      (![X10 : $i, X11 : $i]:
% 1.80/2.00         (~ (v4_relat_1 @ X10 @ X11)
% 1.80/2.00          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 1.80/2.00          | ~ (v1_relat_1 @ X10))),
% 1.80/2.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.80/2.00  thf('16', plain,
% 1.80/2.00      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 1.80/2.00      inference('sup-', [status(thm)], ['14', '15'])).
% 1.80/2.00  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 1.80/2.00      inference('sup-', [status(thm)], ['2', '3'])).
% 1.80/2.00  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 1.80/2.00      inference('demod', [status(thm)], ['16', '17'])).
% 1.80/2.00  thf('19', plain,
% 1.80/2.00      (![X17 : $i]:
% 1.80/2.00         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 1.80/2.00          | ~ (v1_funct_1 @ X17)
% 1.80/2.00          | ~ (v1_relat_1 @ X17))),
% 1.80/2.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.80/2.00  thf(t55_funct_1, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.80/2.00       ( ( v2_funct_1 @ A ) =>
% 1.80/2.00         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.80/2.00           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.80/2.00  thf('20', plain,
% 1.80/2.00      (![X22 : $i]:
% 1.80/2.00         (~ (v2_funct_1 @ X22)
% 1.80/2.00          | ((k1_relat_1 @ X22) = (k2_relat_1 @ (k2_funct_1 @ X22)))
% 1.80/2.00          | ~ (v1_funct_1 @ X22)
% 1.80/2.00          | ~ (v1_relat_1 @ X22))),
% 1.80/2.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.80/2.00  thf('21', plain,
% 1.80/2.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf(redefinition_k2_relset_1, axiom,
% 1.80/2.00    (![A:$i,B:$i,C:$i]:
% 1.80/2.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.80/2.00       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.80/2.00  thf('22', plain,
% 1.80/2.00      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.80/2.00         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 1.80/2.00          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.80/2.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.80/2.00  thf('23', plain,
% 1.80/2.00      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 1.80/2.00      inference('sup-', [status(thm)], ['21', '22'])).
% 1.80/2.00  thf('24', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf('25', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.80/2.00      inference('sup+', [status(thm)], ['23', '24'])).
% 1.80/2.00  thf('26', plain,
% 1.80/2.00      (![X17 : $i]:
% 1.80/2.00         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 1.80/2.00          | ~ (v1_funct_1 @ X17)
% 1.80/2.00          | ~ (v1_relat_1 @ X17))),
% 1.80/2.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.80/2.00  thf('27', plain,
% 1.80/2.00      (![X17 : $i]:
% 1.80/2.00         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.80/2.00          | ~ (v1_funct_1 @ X17)
% 1.80/2.00          | ~ (v1_relat_1 @ X17))),
% 1.80/2.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.80/2.00  thf('28', plain,
% 1.80/2.00      (![X22 : $i]:
% 1.80/2.00         (~ (v2_funct_1 @ X22)
% 1.80/2.00          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 1.80/2.00          | ~ (v1_funct_1 @ X22)
% 1.80/2.00          | ~ (v1_relat_1 @ X22))),
% 1.80/2.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.80/2.00  thf(t3_funct_2, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.80/2.00       ( ( v1_funct_1 @ A ) & 
% 1.80/2.00         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.80/2.00         ( m1_subset_1 @
% 1.80/2.00           A @ 
% 1.80/2.00           ( k1_zfmisc_1 @
% 1.80/2.00             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.80/2.00  thf('29', plain,
% 1.80/2.00      (![X40 : $i]:
% 1.80/2.00         ((m1_subset_1 @ X40 @ 
% 1.80/2.00           (k1_zfmisc_1 @ 
% 1.80/2.00            (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))))
% 1.80/2.00          | ~ (v1_funct_1 @ X40)
% 1.80/2.00          | ~ (v1_relat_1 @ X40))),
% 1.80/2.00      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.80/2.00  thf('30', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.80/2.00           (k1_zfmisc_1 @ 
% 1.80/2.00            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.80/2.00          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.80/2.00      inference('sup+', [status(thm)], ['28', '29'])).
% 1.80/2.00  thf('31', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.80/2.00             (k1_zfmisc_1 @ 
% 1.80/2.00              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.80/2.00               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.80/2.00      inference('sup-', [status(thm)], ['27', '30'])).
% 1.80/2.00  thf('32', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.80/2.00           (k1_zfmisc_1 @ 
% 1.80/2.00            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0))),
% 1.80/2.00      inference('simplify', [status(thm)], ['31'])).
% 1.80/2.00  thf('33', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.80/2.00             (k1_zfmisc_1 @ 
% 1.80/2.00              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.80/2.00               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.80/2.00      inference('sup-', [status(thm)], ['26', '32'])).
% 1.80/2.00  thf('34', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.80/2.00           (k1_zfmisc_1 @ 
% 1.80/2.00            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0))),
% 1.80/2.00      inference('simplify', [status(thm)], ['33'])).
% 1.80/2.00  thf('35', plain,
% 1.80/2.00      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00         (k1_zfmisc_1 @ 
% 1.80/2.00          (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))
% 1.80/2.00        | ~ (v1_relat_1 @ sk_C_1)
% 1.80/2.00        | ~ (v1_funct_1 @ sk_C_1)
% 1.80/2.00        | ~ (v2_funct_1 @ sk_C_1))),
% 1.80/2.00      inference('sup+', [status(thm)], ['25', '34'])).
% 1.80/2.00  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 1.80/2.00      inference('sup-', [status(thm)], ['2', '3'])).
% 1.80/2.00  thf('37', plain, ((v1_funct_1 @ sk_C_1)),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf('38', plain, ((v2_funct_1 @ sk_C_1)),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf('39', plain,
% 1.80/2.00      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00        (k1_zfmisc_1 @ 
% 1.80/2.00         (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 1.80/2.00      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.80/2.00  thf('40', plain,
% 1.80/2.00      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C_1))))
% 1.80/2.00        | ~ (v1_relat_1 @ sk_C_1)
% 1.80/2.00        | ~ (v1_funct_1 @ sk_C_1)
% 1.80/2.00        | ~ (v2_funct_1 @ sk_C_1))),
% 1.80/2.00      inference('sup+', [status(thm)], ['20', '39'])).
% 1.80/2.00  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 1.80/2.00      inference('sup-', [status(thm)], ['2', '3'])).
% 1.80/2.00  thf('42', plain, ((v1_funct_1 @ sk_C_1)),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf('43', plain, ((v2_funct_1 @ sk_C_1)),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf('44', plain,
% 1.80/2.00      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C_1))))),
% 1.80/2.00      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 1.80/2.00  thf(t9_funct_2, axiom,
% 1.80/2.00    (![A:$i,B:$i,C:$i,D:$i]:
% 1.80/2.00     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.80/2.00         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.80/2.00       ( ( r1_tarski @ B @ C ) =>
% 1.80/2.00         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 1.80/2.00             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 1.80/2.00           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.80/2.00  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.80/2.00  thf(zf_stmt_2, axiom,
% 1.80/2.00    (![B:$i,A:$i]:
% 1.80/2.00     ( ( zip_tseitin_1 @ B @ A ) =>
% 1.80/2.00       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 1.80/2.00  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 1.80/2.00  thf(zf_stmt_4, axiom,
% 1.80/2.00    (![D:$i,C:$i,A:$i]:
% 1.80/2.00     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 1.80/2.00       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.80/2.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 1.80/2.00  thf(zf_stmt_5, axiom,
% 1.80/2.00    (![A:$i,B:$i,C:$i,D:$i]:
% 1.80/2.00     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.80/2.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.80/2.00       ( ( r1_tarski @ B @ C ) =>
% 1.80/2.00         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 1.80/2.00  thf('45', plain,
% 1.80/2.00      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.80/2.00         (~ (r1_tarski @ X46 @ X47)
% 1.80/2.00          | (zip_tseitin_1 @ X46 @ X48)
% 1.80/2.00          | ~ (v1_funct_1 @ X49)
% 1.80/2.00          | ~ (v1_funct_2 @ X49 @ X48 @ X46)
% 1.80/2.00          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 1.80/2.00          | (zip_tseitin_0 @ X49 @ X47 @ X48))),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.80/2.00  thf('46', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B_1)
% 1.80/2.00          | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 1.80/2.00               (k1_relat_1 @ sk_C_1))
% 1.80/2.00          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.80/2.00          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 1.80/2.00          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 1.80/2.00      inference('sup-', [status(thm)], ['44', '45'])).
% 1.80/2.00  thf('47', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.80/2.00      inference('sup+', [status(thm)], ['23', '24'])).
% 1.80/2.00  thf('48', plain,
% 1.80/2.00      (![X22 : $i]:
% 1.80/2.00         (~ (v2_funct_1 @ X22)
% 1.80/2.00          | ((k1_relat_1 @ X22) = (k2_relat_1 @ (k2_funct_1 @ X22)))
% 1.80/2.00          | ~ (v1_funct_1 @ X22)
% 1.80/2.00          | ~ (v1_relat_1 @ X22))),
% 1.80/2.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.80/2.00  thf('49', plain,
% 1.80/2.00      (![X17 : $i]:
% 1.80/2.00         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 1.80/2.00          | ~ (v1_funct_1 @ X17)
% 1.80/2.00          | ~ (v1_relat_1 @ X17))),
% 1.80/2.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.80/2.00  thf('50', plain,
% 1.80/2.00      (![X17 : $i]:
% 1.80/2.00         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.80/2.00          | ~ (v1_funct_1 @ X17)
% 1.80/2.00          | ~ (v1_relat_1 @ X17))),
% 1.80/2.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.80/2.00  thf('51', plain,
% 1.80/2.00      (![X22 : $i]:
% 1.80/2.00         (~ (v2_funct_1 @ X22)
% 1.80/2.00          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 1.80/2.00          | ~ (v1_funct_1 @ X22)
% 1.80/2.00          | ~ (v1_relat_1 @ X22))),
% 1.80/2.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.80/2.00  thf('52', plain,
% 1.80/2.00      (![X40 : $i]:
% 1.80/2.00         ((v1_funct_2 @ X40 @ (k1_relat_1 @ X40) @ (k2_relat_1 @ X40))
% 1.80/2.00          | ~ (v1_funct_1 @ X40)
% 1.80/2.00          | ~ (v1_relat_1 @ X40))),
% 1.80/2.00      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.80/2.00  thf('53', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.80/2.00           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.80/2.00          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.80/2.00      inference('sup+', [status(thm)], ['51', '52'])).
% 1.80/2.00  thf('54', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.80/2.00             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.80/2.00      inference('sup-', [status(thm)], ['50', '53'])).
% 1.80/2.00  thf('55', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.80/2.00           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0))),
% 1.80/2.00      inference('simplify', [status(thm)], ['54'])).
% 1.80/2.00  thf('56', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.80/2.00             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.80/2.00      inference('sup-', [status(thm)], ['49', '55'])).
% 1.80/2.00  thf('57', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.80/2.00           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0))),
% 1.80/2.00      inference('simplify', [status(thm)], ['56'])).
% 1.80/2.00  thf('58', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.80/2.00           (k1_relat_1 @ X0))
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v2_funct_1 @ X0))),
% 1.80/2.00      inference('sup+', [status(thm)], ['48', '57'])).
% 1.80/2.00  thf('59', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.80/2.00             (k1_relat_1 @ X0)))),
% 1.80/2.00      inference('simplify', [status(thm)], ['58'])).
% 1.80/2.00  thf('60', plain,
% 1.80/2.00      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ (k1_relat_1 @ sk_C_1))
% 1.80/2.00        | ~ (v1_relat_1 @ sk_C_1)
% 1.80/2.00        | ~ (v1_funct_1 @ sk_C_1)
% 1.80/2.00        | ~ (v2_funct_1 @ sk_C_1))),
% 1.80/2.00      inference('sup+', [status(thm)], ['47', '59'])).
% 1.80/2.00  thf('61', plain, ((v1_relat_1 @ sk_C_1)),
% 1.80/2.00      inference('sup-', [status(thm)], ['2', '3'])).
% 1.80/2.00  thf('62', plain, ((v1_funct_1 @ sk_C_1)),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf('63', plain, ((v2_funct_1 @ sk_C_1)),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf('64', plain,
% 1.80/2.00      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ (k1_relat_1 @ sk_C_1))),
% 1.80/2.00      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 1.80/2.00  thf('65', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B_1)
% 1.80/2.00          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.80/2.00          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 1.80/2.00          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 1.80/2.00      inference('demod', [status(thm)], ['46', '64'])).
% 1.80/2.00  thf('66', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (v1_relat_1 @ sk_C_1)
% 1.80/2.00          | ~ (v1_funct_1 @ sk_C_1)
% 1.80/2.00          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 1.80/2.00          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 1.80/2.00          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B_1))),
% 1.80/2.00      inference('sup-', [status(thm)], ['19', '65'])).
% 1.80/2.00  thf('67', plain, ((v1_relat_1 @ sk_C_1)),
% 1.80/2.00      inference('sup-', [status(thm)], ['2', '3'])).
% 1.80/2.00  thf('68', plain, ((v1_funct_1 @ sk_C_1)),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.00  thf('69', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 1.80/2.00          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 1.80/2.00          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B_1))),
% 1.80/2.00      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.80/2.00  thf('70', plain,
% 1.80/2.00      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B_1)
% 1.80/2.00        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1))),
% 1.80/2.00      inference('sup-', [status(thm)], ['18', '69'])).
% 1.80/2.00  thf('71', plain,
% 1.80/2.00      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.80/2.00         ((v1_funct_2 @ X41 @ X43 @ X42) | ~ (zip_tseitin_0 @ X41 @ X42 @ X43))),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.80/2.00  thf('72', plain,
% 1.80/2.00      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 1.80/2.00        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))),
% 1.80/2.00      inference('sup-', [status(thm)], ['70', '71'])).
% 1.80/2.00  thf('73', plain,
% 1.80/2.00      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('split', [status(esa)], ['0'])).
% 1.80/2.00  thf('74', plain,
% 1.80/2.00      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('sup-', [status(thm)], ['72', '73'])).
% 1.80/2.00  thf('75', plain,
% 1.80/2.00      (![X44 : $i, X45 : $i]:
% 1.80/2.00         (((X44) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X44 @ X45))),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.80/2.00  thf('76', plain,
% 1.80/2.00      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('sup-', [status(thm)], ['74', '75'])).
% 1.80/2.00  thf(t64_relat_1, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( v1_relat_1 @ A ) =>
% 1.80/2.00       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.80/2.00           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.80/2.00         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.80/2.00  thf('77', plain,
% 1.80/2.00      (![X12 : $i]:
% 1.80/2.00         (((k1_relat_1 @ X12) != (k1_xboole_0))
% 1.80/2.00          | ((X12) = (k1_xboole_0))
% 1.80/2.00          | ~ (v1_relat_1 @ X12))),
% 1.80/2.00      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.80/2.00  thf('78', plain,
% 1.80/2.00      (((((k1_xboole_0) != (k1_xboole_0))
% 1.80/2.00         | ~ (v1_relat_1 @ sk_C_1)
% 1.80/2.00         | ((sk_C_1) = (k1_xboole_0))))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('sup-', [status(thm)], ['76', '77'])).
% 1.80/2.00  thf('79', plain, ((v1_relat_1 @ sk_C_1)),
% 1.80/2.00      inference('sup-', [status(thm)], ['2', '3'])).
% 1.80/2.00  thf('80', plain,
% 1.80/2.00      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0))))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('demod', [status(thm)], ['78', '79'])).
% 1.80/2.00  thf('81', plain,
% 1.80/2.00      ((((sk_C_1) = (k1_xboole_0)))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('simplify', [status(thm)], ['80'])).
% 1.80/2.00  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 1.80/2.00  thf('82', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.80/2.00      inference('cnf', [status(esa)], [t81_relat_1])).
% 1.80/2.00  thf(redefinition_k6_partfun1, axiom,
% 1.80/2.00    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.80/2.00  thf('83', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.80/2.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.00  thf('84', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.80/2.00      inference('demod', [status(thm)], ['82', '83'])).
% 1.80/2.00  thf(t71_relat_1, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.80/2.00       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.80/2.00  thf('85', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 1.80/2.00      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.80/2.00  thf('86', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.80/2.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.00  thf('87', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 1.80/2.00      inference('demod', [status(thm)], ['85', '86'])).
% 1.80/2.00  thf(t80_relat_1, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( v1_relat_1 @ A ) =>
% 1.80/2.00       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.80/2.00  thf('88', plain,
% 1.80/2.00      (![X16 : $i]:
% 1.80/2.00         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 1.80/2.00          | ~ (v1_relat_1 @ X16))),
% 1.80/2.00      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.80/2.00  thf('89', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.80/2.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.00  thf('90', plain,
% 1.80/2.00      (![X16 : $i]:
% 1.80/2.00         (((k5_relat_1 @ X16 @ (k6_partfun1 @ (k2_relat_1 @ X16))) = (X16))
% 1.80/2.00          | ~ (v1_relat_1 @ X16))),
% 1.80/2.00      inference('demod', [status(thm)], ['88', '89'])).
% 1.80/2.00  thf('91', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.80/2.00            = (k6_partfun1 @ X0))
% 1.80/2.00          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.80/2.00      inference('sup+', [status(thm)], ['87', '90'])).
% 1.80/2.00  thf(fc3_funct_1, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.80/2.00       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.80/2.00  thf('92', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 1.80/2.00      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.80/2.00  thf('93', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.80/2.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.00  thf('94', plain, (![X18 : $i]: (v1_relat_1 @ (k6_partfun1 @ X18))),
% 1.80/2.00      inference('demod', [status(thm)], ['92', '93'])).
% 1.80/2.00  thf('95', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.80/2.00           = (k6_partfun1 @ X0))),
% 1.80/2.00      inference('demod', [status(thm)], ['91', '94'])).
% 1.80/2.00  thf(t63_funct_1, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.80/2.00       ( ![B:$i]:
% 1.80/2.00         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.80/2.00           ( ( ( v2_funct_1 @ A ) & 
% 1.80/2.00               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.80/2.00               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 1.80/2.00             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.80/2.00  thf('96', plain,
% 1.80/2.00      (![X23 : $i, X24 : $i]:
% 1.80/2.00         (~ (v1_relat_1 @ X23)
% 1.80/2.00          | ~ (v1_funct_1 @ X23)
% 1.80/2.00          | ((X23) = (k2_funct_1 @ X24))
% 1.80/2.00          | ((k5_relat_1 @ X24 @ X23) != (k6_relat_1 @ (k1_relat_1 @ X24)))
% 1.80/2.00          | ((k2_relat_1 @ X24) != (k1_relat_1 @ X23))
% 1.80/2.00          | ~ (v2_funct_1 @ X24)
% 1.80/2.00          | ~ (v1_funct_1 @ X24)
% 1.80/2.00          | ~ (v1_relat_1 @ X24))),
% 1.80/2.00      inference('cnf', [status(esa)], [t63_funct_1])).
% 1.80/2.00  thf('97', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.80/2.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.00  thf('98', plain,
% 1.80/2.00      (![X23 : $i, X24 : $i]:
% 1.80/2.00         (~ (v1_relat_1 @ X23)
% 1.80/2.00          | ~ (v1_funct_1 @ X23)
% 1.80/2.00          | ((X23) = (k2_funct_1 @ X24))
% 1.80/2.00          | ((k5_relat_1 @ X24 @ X23) != (k6_partfun1 @ (k1_relat_1 @ X24)))
% 1.80/2.00          | ((k2_relat_1 @ X24) != (k1_relat_1 @ X23))
% 1.80/2.00          | ~ (v2_funct_1 @ X24)
% 1.80/2.00          | ~ (v1_funct_1 @ X24)
% 1.80/2.00          | ~ (v1_relat_1 @ X24))),
% 1.80/2.00      inference('demod', [status(thm)], ['96', '97'])).
% 1.80/2.00  thf('99', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (((k6_partfun1 @ X0)
% 1.80/2.00            != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 1.80/2.00          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.80/2.00          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 1.80/2.00          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 1.80/2.00          | ((k2_relat_1 @ (k6_partfun1 @ X0))
% 1.80/2.00              != (k1_relat_1 @ (k6_partfun1 @ X0)))
% 1.80/2.00          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 1.80/2.00          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 1.80/2.00          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.80/2.00      inference('sup-', [status(thm)], ['95', '98'])).
% 1.80/2.00  thf('100', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 1.80/2.00      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.80/2.00  thf('101', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.80/2.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.00  thf('102', plain,
% 1.80/2.00      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.80/2.00      inference('demod', [status(thm)], ['100', '101'])).
% 1.80/2.00  thf('103', plain, (![X18 : $i]: (v1_relat_1 @ (k6_partfun1 @ X18))),
% 1.80/2.00      inference('demod', [status(thm)], ['92', '93'])).
% 1.80/2.00  thf('104', plain, (![X19 : $i]: (v1_funct_1 @ (k6_relat_1 @ X19))),
% 1.80/2.00      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.80/2.00  thf('105', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.80/2.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.00  thf('106', plain, (![X19 : $i]: (v1_funct_1 @ (k6_partfun1 @ X19))),
% 1.80/2.00      inference('demod', [status(thm)], ['104', '105'])).
% 1.80/2.00  thf('107', plain,
% 1.80/2.00      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.80/2.00      inference('demod', [status(thm)], ['100', '101'])).
% 1.80/2.00  thf('108', plain,
% 1.80/2.00      (![X16 : $i]:
% 1.80/2.00         (((k5_relat_1 @ X16 @ (k6_partfun1 @ (k2_relat_1 @ X16))) = (X16))
% 1.80/2.00          | ~ (v1_relat_1 @ X16))),
% 1.80/2.00      inference('demod', [status(thm)], ['88', '89'])).
% 1.80/2.00  thf(t53_funct_1, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.80/2.00       ( ( ?[B:$i]:
% 1.80/2.00           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.80/2.00             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 1.80/2.00         ( v2_funct_1 @ A ) ) ))).
% 1.80/2.00  thf('109', plain,
% 1.80/2.00      (![X20 : $i, X21 : $i]:
% 1.80/2.00         (~ (v1_relat_1 @ X20)
% 1.80/2.00          | ~ (v1_funct_1 @ X20)
% 1.80/2.00          | ((k5_relat_1 @ X21 @ X20) != (k6_relat_1 @ (k1_relat_1 @ X21)))
% 1.80/2.00          | (v2_funct_1 @ X21)
% 1.80/2.00          | ~ (v1_funct_1 @ X21)
% 1.80/2.00          | ~ (v1_relat_1 @ X21))),
% 1.80/2.00      inference('cnf', [status(esa)], [t53_funct_1])).
% 1.80/2.00  thf('110', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 1.80/2.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.80/2.00  thf('111', plain,
% 1.80/2.00      (![X20 : $i, X21 : $i]:
% 1.80/2.00         (~ (v1_relat_1 @ X20)
% 1.80/2.00          | ~ (v1_funct_1 @ X20)
% 1.80/2.00          | ((k5_relat_1 @ X21 @ X20) != (k6_partfun1 @ (k1_relat_1 @ X21)))
% 1.80/2.00          | (v2_funct_1 @ X21)
% 1.80/2.00          | ~ (v1_funct_1 @ X21)
% 1.80/2.00          | ~ (v1_relat_1 @ X21))),
% 1.80/2.00      inference('demod', [status(thm)], ['109', '110'])).
% 1.80/2.00  thf('112', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (((X0) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | (v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.80/2.00          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 1.80/2.00      inference('sup-', [status(thm)], ['108', '111'])).
% 1.80/2.00  thf('113', plain, (![X19 : $i]: (v1_funct_1 @ (k6_partfun1 @ X19))),
% 1.80/2.00      inference('demod', [status(thm)], ['104', '105'])).
% 1.80/2.00  thf('114', plain, (![X18 : $i]: (v1_relat_1 @ (k6_partfun1 @ X18))),
% 1.80/2.00      inference('demod', [status(thm)], ['92', '93'])).
% 1.80/2.00  thf('115', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (((X0) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | (v2_funct_1 @ X0))),
% 1.80/2.00      inference('demod', [status(thm)], ['112', '113', '114'])).
% 1.80/2.00  thf('116', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         ((v2_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_funct_1 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ X0)
% 1.80/2.00          | ((X0) != (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 1.80/2.00      inference('simplify', [status(thm)], ['115'])).
% 1.80/2.00  thf('117', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 1.80/2.00          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.80/2.00          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 1.80/2.00          | (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 1.80/2.00      inference('sup-', [status(thm)], ['107', '116'])).
% 1.80/2.00  thf('118', plain, (![X18 : $i]: (v1_relat_1 @ (k6_partfun1 @ X18))),
% 1.80/2.00      inference('demod', [status(thm)], ['92', '93'])).
% 1.80/2.00  thf('119', plain, (![X19 : $i]: (v1_funct_1 @ (k6_partfun1 @ X19))),
% 1.80/2.00      inference('demod', [status(thm)], ['104', '105'])).
% 1.80/2.00  thf('120', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 1.80/2.00          | (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 1.80/2.00      inference('demod', [status(thm)], ['117', '118', '119'])).
% 1.80/2.00  thf('121', plain, (![X0 : $i]: (v2_funct_1 @ (k6_partfun1 @ X0))),
% 1.80/2.00      inference('simplify', [status(thm)], ['120'])).
% 1.80/2.00  thf('122', plain,
% 1.80/2.00      (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 1.80/2.00      inference('demod', [status(thm)], ['85', '86'])).
% 1.80/2.00  thf('123', plain,
% 1.80/2.00      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.80/2.00      inference('demod', [status(thm)], ['100', '101'])).
% 1.80/2.00  thf('124', plain, (![X19 : $i]: (v1_funct_1 @ (k6_partfun1 @ X19))),
% 1.80/2.00      inference('demod', [status(thm)], ['104', '105'])).
% 1.80/2.00  thf('125', plain, (![X18 : $i]: (v1_relat_1 @ (k6_partfun1 @ X18))),
% 1.80/2.00      inference('demod', [status(thm)], ['92', '93'])).
% 1.80/2.00  thf('126', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 1.80/2.00          | ((X0) != (X0))
% 1.80/2.00          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0))))),
% 1.80/2.00      inference('demod', [status(thm)],
% 1.80/2.00                ['99', '102', '103', '106', '121', '122', '123', '124', '125'])).
% 1.80/2.00  thf('127', plain,
% 1.80/2.00      (![X0 : $i]: ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))),
% 1.80/2.00      inference('simplify', [status(thm)], ['126'])).
% 1.80/2.00  thf('128', plain,
% 1.80/2.00      (((k6_partfun1 @ k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 1.80/2.00      inference('sup+', [status(thm)], ['84', '127'])).
% 1.80/2.00  thf('129', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.80/2.00      inference('demod', [status(thm)], ['82', '83'])).
% 1.80/2.00  thf('130', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 1.80/2.00      inference('demod', [status(thm)], ['128', '129'])).
% 1.80/2.00  thf('131', plain,
% 1.80/2.00      ((~ (v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ sk_A))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('demod', [status(thm)], ['11', '81', '130'])).
% 1.80/2.00  thf('132', plain,
% 1.80/2.00      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('sup-', [status(thm)], ['74', '75'])).
% 1.80/2.00  thf(t65_relat_1, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( v1_relat_1 @ A ) =>
% 1.80/2.00       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 1.80/2.00         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 1.80/2.00  thf('133', plain,
% 1.80/2.00      (![X13 : $i]:
% 1.80/2.00         (((k1_relat_1 @ X13) != (k1_xboole_0))
% 1.80/2.00          | ((k2_relat_1 @ X13) = (k1_xboole_0))
% 1.80/2.00          | ~ (v1_relat_1 @ X13))),
% 1.80/2.00      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.80/2.00  thf('134', plain,
% 1.80/2.00      (((((k1_xboole_0) != (k1_xboole_0))
% 1.80/2.00         | ~ (v1_relat_1 @ sk_C_1)
% 1.80/2.00         | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0))))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('sup-', [status(thm)], ['132', '133'])).
% 1.80/2.00  thf('135', plain, ((v1_relat_1 @ sk_C_1)),
% 1.80/2.00      inference('sup-', [status(thm)], ['2', '3'])).
% 1.80/2.00  thf('136', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 1.80/2.00      inference('sup+', [status(thm)], ['23', '24'])).
% 1.80/2.00  thf('137', plain,
% 1.80/2.00      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.80/2.00  thf('138', plain,
% 1.80/2.00      ((((sk_B_1) = (k1_xboole_0)))
% 1.80/2.00         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('simplify', [status(thm)], ['137'])).
% 1.80/2.00  thf('139', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.80/2.00      inference('demod', [status(thm)], ['82', '83'])).
% 1.80/2.00  thf(dt_k6_partfun1, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( m1_subset_1 @
% 1.80/2.00         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.80/2.00       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.80/2.00  thf('140', plain, (![X37 : $i]: (v1_partfun1 @ (k6_partfun1 @ X37) @ X37)),
% 1.80/2.00      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.80/2.00  thf('141', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 1.80/2.00      inference('sup+', [status(thm)], ['139', '140'])).
% 1.80/2.00  thf(d3_tarski, axiom,
% 1.80/2.00    (![A:$i,B:$i]:
% 1.80/2.00     ( ( r1_tarski @ A @ B ) <=>
% 1.80/2.00       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.80/2.00  thf('142', plain,
% 1.80/2.00      (![X4 : $i, X6 : $i]:
% 1.80/2.00         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.80/2.00      inference('cnf', [status(esa)], [d3_tarski])).
% 1.80/2.00  thf(d1_xboole_0, axiom,
% 1.80/2.00    (![A:$i]:
% 1.80/2.00     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.80/2.00  thf('143', plain,
% 1.80/2.00      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.80/2.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.80/2.00  thf('144', plain,
% 1.80/2.00      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.80/2.00      inference('sup-', [status(thm)], ['142', '143'])).
% 1.80/2.00  thf('145', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.80/2.00      inference('demod', [status(thm)], ['82', '83'])).
% 1.80/2.00  thf('146', plain,
% 1.80/2.00      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.80/2.00      inference('demod', [status(thm)], ['100', '101'])).
% 1.80/2.00  thf('147', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.80/2.00      inference('sup+', [status(thm)], ['145', '146'])).
% 1.80/2.00  thf('148', plain,
% 1.80/2.00      (![X10 : $i, X11 : $i]:
% 1.80/2.00         (~ (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 1.80/2.00          | (v4_relat_1 @ X10 @ X11)
% 1.80/2.00          | ~ (v1_relat_1 @ X10))),
% 1.80/2.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.80/2.00  thf('149', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.80/2.00          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.80/2.00          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 1.80/2.00      inference('sup-', [status(thm)], ['147', '148'])).
% 1.80/2.00  thf('150', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.80/2.00      inference('demod', [status(thm)], ['82', '83'])).
% 1.80/2.00  thf('151', plain, (![X18 : $i]: (v1_relat_1 @ (k6_partfun1 @ X18))),
% 1.80/2.00      inference('demod', [status(thm)], ['92', '93'])).
% 1.80/2.00  thf('152', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.80/2.00      inference('sup+', [status(thm)], ['150', '151'])).
% 1.80/2.00  thf('153', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (r1_tarski @ k1_xboole_0 @ X0) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 1.80/2.00      inference('demod', [status(thm)], ['149', '152'])).
% 1.80/2.00  thf('154', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (v1_xboole_0 @ k1_xboole_0) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 1.80/2.00      inference('sup-', [status(thm)], ['144', '153'])).
% 1.80/2.00  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.80/2.00  thf('155', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.80/2.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.80/2.00  thf('156', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 1.80/2.00      inference('demod', [status(thm)], ['154', '155'])).
% 1.80/2.00  thf('157', plain,
% 1.80/2.00      (![X10 : $i, X11 : $i]:
% 1.80/2.00         (~ (v4_relat_1 @ X10 @ X11)
% 1.80/2.00          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 1.80/2.00          | ~ (v1_relat_1 @ X10))),
% 1.80/2.00      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.80/2.00  thf('158', plain,
% 1.80/2.00      (![X0 : $i]:
% 1.80/2.00         (~ (v1_relat_1 @ k1_xboole_0)
% 1.80/2.00          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.80/2.00      inference('sup-', [status(thm)], ['156', '157'])).
% 1.80/2.00  thf('159', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.80/2.00      inference('sup+', [status(thm)], ['150', '151'])).
% 1.80/2.00  thf('160', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.80/2.00      inference('sup+', [status(thm)], ['145', '146'])).
% 1.80/2.00  thf('161', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.80/2.00      inference('demod', [status(thm)], ['158', '159', '160'])).
% 1.80/2.00  thf(t3_subset, axiom,
% 1.80/2.00    (![A:$i,B:$i]:
% 1.80/2.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.80/2.00  thf('162', plain,
% 1.80/2.00      (![X7 : $i, X9 : $i]:
% 1.80/2.00         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.80/2.00      inference('cnf', [status(esa)], [t3_subset])).
% 1.80/2.00  thf('163', plain,
% 1.80/2.00      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.80/2.00      inference('sup-', [status(thm)], ['161', '162'])).
% 1.80/2.00  thf(cc1_funct_2, axiom,
% 1.80/2.00    (![A:$i,B:$i,C:$i]:
% 1.80/2.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.80/2.00       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 1.80/2.00         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 1.80/2.00  thf('164', plain,
% 1.80/2.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.80/2.00         (~ (v1_funct_1 @ X34)
% 1.80/2.00          | ~ (v1_partfun1 @ X34 @ X35)
% 1.80/2.00          | (v1_funct_2 @ X34 @ X35 @ X36)
% 1.80/2.00          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.80/2.00      inference('cnf', [status(esa)], [cc1_funct_2])).
% 1.80/2.00  thf('165', plain,
% 1.80/2.00      (![X0 : $i, X1 : $i]:
% 1.80/2.00         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 1.80/2.00          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 1.80/2.00          | ~ (v1_funct_1 @ k1_xboole_0))),
% 1.80/2.00      inference('sup-', [status(thm)], ['163', '164'])).
% 1.80/2.00  thf('166', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.80/2.00      inference('demod', [status(thm)], ['82', '83'])).
% 1.80/2.00  thf('167', plain, (![X19 : $i]: (v1_funct_1 @ (k6_partfun1 @ X19))),
% 1.80/2.00      inference('demod', [status(thm)], ['104', '105'])).
% 1.80/2.00  thf('168', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.80/2.00      inference('sup+', [status(thm)], ['166', '167'])).
% 1.80/2.00  thf('169', plain,
% 1.80/2.00      (![X0 : $i, X1 : $i]:
% 1.80/2.00         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 1.80/2.00          | ~ (v1_partfun1 @ k1_xboole_0 @ X1))),
% 1.80/2.00      inference('demod', [status(thm)], ['165', '168'])).
% 1.80/2.00  thf('170', plain,
% 1.80/2.00      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.80/2.00      inference('sup-', [status(thm)], ['141', '169'])).
% 1.80/2.00  thf('171', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))),
% 1.80/2.00      inference('demod', [status(thm)], ['131', '138', '170'])).
% 1.80/2.00  thf('172', plain,
% 1.80/2.00      (~
% 1.80/2.00       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 1.80/2.00       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)) | 
% 1.80/2.00       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.80/2.00      inference('split', [status(esa)], ['0'])).
% 1.80/2.00  thf('173', plain,
% 1.80/2.00      (~
% 1.80/2.00       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 1.80/2.00      inference('sat_resolution*', [status(thm)], ['10', '171', '172'])).
% 1.80/2.00  thf('174', plain,
% 1.80/2.00      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('simpl_trail', [status(thm)], ['1', '173'])).
% 1.80/2.00  thf('175', plain,
% 1.80/2.00      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B_1)
% 1.80/2.00        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1))),
% 1.80/2.00      inference('sup-', [status(thm)], ['18', '69'])).
% 1.80/2.00  thf('176', plain,
% 1.80/2.00      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.80/2.00         ((m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 1.80/2.00          | ~ (zip_tseitin_0 @ X41 @ X42 @ X43))),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.80/2.00  thf('177', plain,
% 1.80/2.00      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 1.80/2.00        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 1.80/2.00      inference('sup-', [status(thm)], ['175', '176'])).
% 1.80/2.00  thf('178', plain,
% 1.80/2.00      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.80/2.00          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.80/2.00      inference('simpl_trail', [status(thm)], ['1', '173'])).
% 1.80/2.00  thf('179', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)),
% 1.80/2.00      inference('clc', [status(thm)], ['177', '178'])).
% 1.80/2.00  thf('180', plain,
% 1.80/2.00      (![X44 : $i, X45 : $i]:
% 1.80/2.00         (((X44) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X44 @ X45))),
% 1.80/2.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.80/2.00  thf('181', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 1.80/2.00      inference('sup-', [status(thm)], ['179', '180'])).
% 1.80/2.00  thf('182', plain,
% 1.80/2.00      (![X12 : $i]:
% 1.80/2.00         (((k1_relat_1 @ X12) != (k1_xboole_0))
% 1.80/2.00          | ((X12) = (k1_xboole_0))
% 1.80/2.00          | ~ (v1_relat_1 @ X12))),
% 1.80/2.00      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.80/2.00  thf('183', plain,
% 1.80/2.00      ((((k1_xboole_0) != (k1_xboole_0))
% 1.80/2.00        | ~ (v1_relat_1 @ sk_C_1)
% 1.80/2.00        | ((sk_C_1) = (k1_xboole_0)))),
% 1.80/2.00      inference('sup-', [status(thm)], ['181', '182'])).
% 1.80/2.00  thf('184', plain, ((v1_relat_1 @ sk_C_1)),
% 1.80/2.00      inference('sup-', [status(thm)], ['2', '3'])).
% 1.80/2.00  thf('185', plain,
% 1.80/2.00      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 1.80/2.00      inference('demod', [status(thm)], ['183', '184'])).
% 1.80/2.00  thf('186', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.80/2.00      inference('simplify', [status(thm)], ['185'])).
% 1.80/2.00  thf('187', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 1.80/2.00      inference('demod', [status(thm)], ['128', '129'])).
% 1.80/2.00  thf('188', plain,
% 1.80/2.00      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.80/2.00      inference('sup-', [status(thm)], ['161', '162'])).
% 1.80/2.00  thf('189', plain, ($false),
% 1.80/2.00      inference('demod', [status(thm)], ['174', '186', '187', '188'])).
% 1.80/2.00  
% 1.80/2.00  % SZS output end Refutation
% 1.80/2.00  
% 1.80/2.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
