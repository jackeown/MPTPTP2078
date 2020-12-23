%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S5BLATMPm9

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:45 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 918 expanded)
%              Number of leaves         :   44 ( 281 expanded)
%              Depth                    :   19
%              Number of atoms          : 1194 (13710 expanded)
%              Number of equality atoms :  104 ( 589 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ X16 )
        = ( k4_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('20',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k3_relset_1 @ X34 @ X35 @ X33 )
        = ( k4_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('23',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','28','29'])).

thf('31',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['10','30'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,
    ( ( sk_B
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['10','30'])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ( sk_B
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('49',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('53',plain,
    ( ( sk_B != sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','51','52'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('62',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('65',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63','65'])).

thf('67',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('68',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('69',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k3_relset_1 @ X34 @ X35 @ X33 )
        = ( k4_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('72',plain,(
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('73',plain,(
    ! [X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('77',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('78',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','77'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('79',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k3_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('86',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('90',plain,(
    m1_subset_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('92',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('93',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','94'])).

thf('96',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','67','95'])).

thf('97',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 != k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ( X43 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('98',plain,(
    ! [X42: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X42 @ k1_xboole_0 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('100',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('101',plain,(
    ! [X42: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X42 @ k1_xboole_0 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','67','95'])).

thf('103',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('105',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('113',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('115',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['111','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['96','103','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S5BLATMPm9
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:28:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.38/1.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.38/1.62  % Solved by: fo/fo7.sh
% 1.38/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.62  % done 1447 iterations in 1.170s
% 1.38/1.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.38/1.62  % SZS output start Refutation
% 1.38/1.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.38/1.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.38/1.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.38/1.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.38/1.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.38/1.62  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.38/1.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.38/1.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.38/1.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.38/1.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.38/1.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.38/1.62  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 1.38/1.62  thf(sk_C_type, type, sk_C: $i).
% 1.38/1.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.38/1.62  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.38/1.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.38/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.38/1.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.38/1.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.38/1.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.38/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.62  thf(t31_funct_2, conjecture,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.38/1.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.38/1.62       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.38/1.62         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.38/1.62           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.38/1.62           ( m1_subset_1 @
% 1.38/1.62             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.38/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.62    (~( ![A:$i,B:$i,C:$i]:
% 1.38/1.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.38/1.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.38/1.62          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.38/1.62            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.38/1.62              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.38/1.62              ( m1_subset_1 @
% 1.38/1.62                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.38/1.62    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.38/1.62  thf('0', plain,
% 1.38/1.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.38/1.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.38/1.62        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.38/1.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('1', plain,
% 1.38/1.62      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.38/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.38/1.62      inference('split', [status(esa)], ['0'])).
% 1.38/1.62  thf('2', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(cc1_relset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.62       ( v1_relat_1 @ C ) ))).
% 1.38/1.62  thf('3', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.38/1.62         ((v1_relat_1 @ X18)
% 1.38/1.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.38/1.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.38/1.62  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 1.38/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.38/1.62  thf(d9_funct_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.38/1.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.38/1.62  thf('5', plain,
% 1.38/1.62      (![X16 : $i]:
% 1.38/1.62         (~ (v2_funct_1 @ X16)
% 1.38/1.62          | ((k2_funct_1 @ X16) = (k4_relat_1 @ X16))
% 1.38/1.62          | ~ (v1_funct_1 @ X16)
% 1.38/1.62          | ~ (v1_relat_1 @ X16))),
% 1.38/1.62      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.38/1.62  thf('6', plain,
% 1.38/1.62      ((~ (v1_funct_1 @ sk_C)
% 1.38/1.62        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.38/1.62        | ~ (v2_funct_1 @ sk_C))),
% 1.38/1.62      inference('sup-', [status(thm)], ['4', '5'])).
% 1.38/1.62  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.38/1.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.38/1.62  thf('10', plain,
% 1.38/1.62      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 1.38/1.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['1', '9'])).
% 1.38/1.62  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 1.38/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.38/1.62  thf(dt_k2_funct_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.38/1.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.38/1.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.38/1.62  thf('12', plain,
% 1.38/1.62      (![X17 : $i]:
% 1.38/1.62         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 1.38/1.62          | ~ (v1_funct_1 @ X17)
% 1.38/1.62          | ~ (v1_relat_1 @ X17))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.38/1.62  thf('13', plain,
% 1.38/1.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.38/1.62         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.38/1.62      inference('split', [status(esa)], ['0'])).
% 1.38/1.62  thf('14', plain,
% 1.38/1.62      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.38/1.62         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['12', '13'])).
% 1.38/1.62  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('16', plain,
% 1.38/1.62      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.38/1.62      inference('demod', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['11', '16'])).
% 1.38/1.62  thf('18', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(dt_k3_relset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.62       ( m1_subset_1 @
% 1.38/1.62         ( k3_relset_1 @ A @ B @ C ) @ 
% 1.38/1.62         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 1.38/1.62  thf('19', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.38/1.62         ((m1_subset_1 @ (k3_relset_1 @ X24 @ X25 @ X26) @ 
% 1.38/1.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 1.38/1.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 1.38/1.62  thf('20', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['18', '19'])).
% 1.38/1.62  thf('21', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(redefinition_k3_relset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.62       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 1.38/1.62  thf('22', plain,
% 1.38/1.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.38/1.62         (((k3_relset_1 @ X34 @ X35 @ X33) = (k4_relat_1 @ X33))
% 1.38/1.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.38/1.62      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 1.38/1.62  thf('23', plain,
% 1.38/1.62      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.38/1.62      inference('sup-', [status(thm)], ['21', '22'])).
% 1.38/1.62  thf('24', plain,
% 1.38/1.62      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['20', '23'])).
% 1.38/1.62  thf('25', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.38/1.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.38/1.62  thf('26', plain,
% 1.38/1.62      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.38/1.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.38/1.62         <= (~
% 1.38/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.38/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.38/1.62      inference('split', [status(esa)], ['0'])).
% 1.38/1.62  thf('27', plain,
% 1.38/1.62      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.38/1.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.38/1.62         <= (~
% 1.38/1.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.38/1.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['25', '26'])).
% 1.38/1.62  thf('28', plain,
% 1.38/1.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.38/1.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['24', '27'])).
% 1.38/1.62  thf('29', plain,
% 1.38/1.62      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.38/1.62       ~
% 1.38/1.62       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.38/1.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.38/1.62       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.38/1.62      inference('split', [status(esa)], ['0'])).
% 1.38/1.62  thf('30', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.38/1.62      inference('sat_resolution*', [status(thm)], ['17', '28', '29'])).
% 1.38/1.62  thf('31', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 1.38/1.62      inference('simpl_trail', [status(thm)], ['10', '30'])).
% 1.38/1.62  thf(t37_relat_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( v1_relat_1 @ A ) =>
% 1.38/1.62       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.38/1.62         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.38/1.62  thf('32', plain,
% 1.38/1.62      (![X14 : $i]:
% 1.38/1.62         (((k2_relat_1 @ X14) = (k1_relat_1 @ (k4_relat_1 @ X14)))
% 1.38/1.62          | ~ (v1_relat_1 @ X14))),
% 1.38/1.62      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.38/1.62  thf(d1_funct_2, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.38/1.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.38/1.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.38/1.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.38/1.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.38/1.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.38/1.62  thf(zf_stmt_1, axiom,
% 1.38/1.62    (![B:$i,A:$i]:
% 1.38/1.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.38/1.62       ( zip_tseitin_0 @ B @ A ) ))).
% 1.38/1.62  thf('33', plain,
% 1.38/1.62      (![X36 : $i, X37 : $i]:
% 1.38/1.62         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.38/1.62  thf('34', plain,
% 1.38/1.62      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['20', '23'])).
% 1.38/1.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.38/1.62  thf(zf_stmt_3, axiom,
% 1.38/1.62    (![C:$i,B:$i,A:$i]:
% 1.38/1.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.38/1.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.38/1.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.38/1.62  thf(zf_stmt_5, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.38/1.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.38/1.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.38/1.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.38/1.62  thf('35', plain,
% 1.38/1.62      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.38/1.62         (~ (zip_tseitin_0 @ X41 @ X42)
% 1.38/1.62          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 1.38/1.62          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.38/1.62  thf('36', plain,
% 1.38/1.62      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 1.38/1.62        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['34', '35'])).
% 1.38/1.62  thf('37', plain,
% 1.38/1.62      ((((sk_A) = (k1_xboole_0))
% 1.38/1.62        | (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['33', '36'])).
% 1.38/1.62  thf('38', plain,
% 1.38/1.62      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['20', '23'])).
% 1.38/1.62  thf(redefinition_k1_relset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.38/1.62  thf('39', plain,
% 1.38/1.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.38/1.62         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 1.38/1.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.38/1.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.38/1.62  thf('40', plain,
% 1.38/1.62      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C))
% 1.38/1.62         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['38', '39'])).
% 1.38/1.62  thf('41', plain,
% 1.38/1.62      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.38/1.62         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 1.38/1.62          | (v1_funct_2 @ X40 @ X38 @ X39)
% 1.38/1.62          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.38/1.62  thf('42', plain,
% 1.38/1.62      ((((sk_B) != (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.38/1.62        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 1.38/1.62        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['40', '41'])).
% 1.38/1.62  thf('43', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 1.38/1.62      inference('simpl_trail', [status(thm)], ['10', '30'])).
% 1.38/1.62  thf('44', plain,
% 1.38/1.62      ((~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 1.38/1.62        | ((sk_B) != (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 1.38/1.62      inference('clc', [status(thm)], ['42', '43'])).
% 1.38/1.62  thf('45', plain,
% 1.38/1.62      ((((sk_A) = (k1_xboole_0))
% 1.38/1.62        | ((sk_B) != (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['37', '44'])).
% 1.38/1.62  thf('46', plain,
% 1.38/1.62      ((((sk_B) != (k2_relat_1 @ sk_C))
% 1.38/1.62        | ~ (v1_relat_1 @ sk_C)
% 1.38/1.62        | ((sk_A) = (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['32', '45'])).
% 1.38/1.62  thf('47', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(redefinition_k2_relset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.38/1.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.38/1.62  thf('48', plain,
% 1.38/1.62      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.38/1.62         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 1.38/1.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.38/1.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.38/1.62  thf('49', plain,
% 1.38/1.62      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.38/1.62      inference('sup-', [status(thm)], ['47', '48'])).
% 1.38/1.62  thf('50', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('51', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.38/1.62      inference('sup+', [status(thm)], ['49', '50'])).
% 1.38/1.62  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 1.38/1.62      inference('sup-', [status(thm)], ['2', '3'])).
% 1.38/1.62  thf('53', plain, ((((sk_B) != (sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 1.38/1.62      inference('demod', [status(thm)], ['46', '51', '52'])).
% 1.38/1.62  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 1.38/1.62      inference('simplify', [status(thm)], ['53'])).
% 1.38/1.62  thf('55', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ k1_xboole_0)),
% 1.38/1.62      inference('demod', [status(thm)], ['31', '54'])).
% 1.38/1.62  thf('56', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(t3_subset, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.38/1.62  thf('57', plain,
% 1.38/1.62      (![X8 : $i, X9 : $i]:
% 1.38/1.62         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('58', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['56', '57'])).
% 1.38/1.62  thf(t12_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.38/1.62  thf('59', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 1.38/1.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.38/1.62  thf('60', plain,
% 1.38/1.62      (((k2_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.38/1.62         = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['58', '59'])).
% 1.38/1.62  thf(t15_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 1.38/1.62       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.38/1.62  thf('61', plain,
% 1.38/1.62      (![X2 : $i, X3 : $i]:
% 1.38/1.62         (((X2) = (k1_xboole_0)) | ((k2_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t15_xboole_1])).
% 1.38/1.62  thf('62', plain,
% 1.38/1.62      ((((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 1.38/1.62        | ((sk_C) = (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['60', '61'])).
% 1.38/1.62  thf('63', plain, (((sk_A) = (k1_xboole_0))),
% 1.38/1.62      inference('simplify', [status(thm)], ['53'])).
% 1.38/1.62  thf(t113_zfmisc_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.38/1.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.38/1.62  thf('64', plain,
% 1.38/1.62      (![X5 : $i, X6 : $i]:
% 1.38/1.62         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.38/1.62  thf('65', plain,
% 1.38/1.62      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.38/1.62      inference('simplify', [status(thm)], ['64'])).
% 1.38/1.62  thf('66', plain,
% 1.38/1.62      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 1.38/1.62      inference('demod', [status(thm)], ['62', '63', '65'])).
% 1.38/1.62  thf('67', plain, (((sk_C) = (k1_xboole_0))),
% 1.38/1.62      inference('simplify', [status(thm)], ['66'])).
% 1.38/1.62  thf(t4_subset_1, axiom,
% 1.38/1.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.38/1.62  thf('68', plain,
% 1.38/1.62      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.38/1.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.38/1.62  thf('69', plain,
% 1.38/1.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.38/1.62         (((k3_relset_1 @ X34 @ X35 @ X33) = (k4_relat_1 @ X33))
% 1.38/1.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.38/1.62      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 1.38/1.62  thf('70', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k3_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['68', '69'])).
% 1.38/1.62  thf('71', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k3_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['68', '69'])).
% 1.38/1.62  thf('72', plain,
% 1.38/1.62      (![X14 : $i]:
% 1.38/1.62         (((k2_relat_1 @ X14) = (k1_relat_1 @ (k4_relat_1 @ X14)))
% 1.38/1.62          | ~ (v1_relat_1 @ X14))),
% 1.38/1.62      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.38/1.62  thf(t64_relat_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( v1_relat_1 @ A ) =>
% 1.38/1.62       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.38/1.62           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.38/1.62         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.38/1.62  thf('73', plain,
% 1.38/1.62      (![X15 : $i]:
% 1.38/1.62         (((k1_relat_1 @ X15) != (k1_xboole_0))
% 1.38/1.62          | ((X15) = (k1_xboole_0))
% 1.38/1.62          | ~ (v1_relat_1 @ X15))),
% 1.38/1.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.38/1.62  thf('74', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 1.38/1.62          | ~ (v1_relat_1 @ X0)
% 1.38/1.62          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 1.38/1.62          | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['72', '73'])).
% 1.38/1.62  thf('75', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (~ (v1_relat_1 @ (k3_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 1.38/1.62          | ((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.38/1.62          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.38/1.62          | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['71', '74'])).
% 1.38/1.62  thf('76', plain,
% 1.38/1.62      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.38/1.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.38/1.62  thf('77', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.38/1.62         ((v1_relat_1 @ X18)
% 1.38/1.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.38/1.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.38/1.62  thf('78', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.38/1.62      inference('sup-', [status(thm)], ['76', '77'])).
% 1.38/1.62  thf(t60_relat_1, axiom,
% 1.38/1.62    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.38/1.62     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.38/1.62  thf('79', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.38/1.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.38/1.62  thf('80', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (~ (v1_relat_1 @ (k3_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 1.38/1.62          | ((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.38/1.62          | ((k1_xboole_0) != (k1_xboole_0)))),
% 1.38/1.62      inference('demod', [status(thm)], ['75', '78', '79'])).
% 1.38/1.62  thf('81', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.38/1.62          | ~ (v1_relat_1 @ (k3_relset_1 @ X1 @ X0 @ k1_xboole_0)))),
% 1.38/1.62      inference('simplify', [status(thm)], ['80'])).
% 1.38/1.62  thf('82', plain,
% 1.38/1.62      ((~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 1.38/1.62        | ((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['70', '81'])).
% 1.38/1.62  thf('83', plain,
% 1.38/1.62      (![X5 : $i, X6 : $i]:
% 1.38/1.62         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.38/1.62  thf('84', plain,
% 1.38/1.62      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.38/1.62      inference('simplify', [status(thm)], ['83'])).
% 1.38/1.62  thf('85', plain,
% 1.38/1.62      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.38/1.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.38/1.62  thf('86', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.38/1.62         ((m1_subset_1 @ (k3_relset_1 @ X24 @ X25 @ X26) @ 
% 1.38/1.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 1.38/1.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 1.38/1.62  thf('87', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (m1_subset_1 @ (k3_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 1.38/1.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['85', '86'])).
% 1.38/1.62  thf('88', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (m1_subset_1 @ (k3_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) @ 
% 1.38/1.62          (k1_zfmisc_1 @ k1_xboole_0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['84', '87'])).
% 1.38/1.62  thf('89', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k3_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['68', '69'])).
% 1.38/1.62  thf('90', plain,
% 1.38/1.62      ((m1_subset_1 @ (k4_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['88', '89'])).
% 1.38/1.62  thf('91', plain,
% 1.38/1.62      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.38/1.62      inference('simplify', [status(thm)], ['83'])).
% 1.38/1.62  thf('92', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.38/1.62         ((v1_relat_1 @ X18)
% 1.38/1.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.38/1.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.38/1.62  thf('93', plain,
% 1.38/1.62      (![X1 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.38/1.62          | (v1_relat_1 @ X1))),
% 1.38/1.62      inference('sup-', [status(thm)], ['91', '92'])).
% 1.38/1.62  thf('94', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['90', '93'])).
% 1.38/1.62  thf('95', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['82', '94'])).
% 1.38/1.62  thf('96', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ k1_xboole_0)),
% 1.38/1.62      inference('demod', [status(thm)], ['55', '67', '95'])).
% 1.38/1.62  thf('97', plain,
% 1.38/1.62      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.38/1.62         (((X41) != (k1_xboole_0))
% 1.38/1.62          | ((X42) = (k1_xboole_0))
% 1.38/1.62          | (v1_funct_2 @ X43 @ X42 @ X41)
% 1.38/1.62          | ((X43) != (k1_xboole_0))
% 1.38/1.62          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.38/1.62  thf('98', plain,
% 1.38/1.62      (![X42 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 1.38/1.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ k1_xboole_0)))
% 1.38/1.62          | (v1_funct_2 @ k1_xboole_0 @ X42 @ k1_xboole_0)
% 1.38/1.62          | ((X42) = (k1_xboole_0)))),
% 1.38/1.62      inference('simplify', [status(thm)], ['97'])).
% 1.38/1.62  thf('99', plain,
% 1.38/1.62      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.38/1.62      inference('simplify', [status(thm)], ['83'])).
% 1.38/1.62  thf('100', plain,
% 1.38/1.62      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.38/1.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.38/1.62  thf('101', plain,
% 1.38/1.62      (![X42 : $i]:
% 1.38/1.62         ((v1_funct_2 @ k1_xboole_0 @ X42 @ k1_xboole_0)
% 1.38/1.62          | ((X42) = (k1_xboole_0)))),
% 1.38/1.62      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.38/1.62  thf('102', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ k1_xboole_0)),
% 1.38/1.62      inference('demod', [status(thm)], ['55', '67', '95'])).
% 1.38/1.62  thf('103', plain, (((sk_B) = (k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['101', '102'])).
% 1.38/1.62  thf('104', plain,
% 1.38/1.62      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.38/1.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.38/1.62  thf('105', plain,
% 1.38/1.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.38/1.62         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 1.38/1.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.38/1.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.38/1.62  thf('106', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['104', '105'])).
% 1.38/1.62  thf('107', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.38/1.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.38/1.62  thf('108', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['106', '107'])).
% 1.38/1.62  thf('109', plain,
% 1.38/1.62      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.38/1.62         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 1.38/1.62          | (v1_funct_2 @ X40 @ X38 @ X39)
% 1.38/1.62          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.38/1.62  thf('110', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (((X1) != (k1_xboole_0))
% 1.38/1.62          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.38/1.62          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['108', '109'])).
% 1.38/1.62  thf('111', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.38/1.62          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.38/1.62      inference('simplify', [status(thm)], ['110'])).
% 1.38/1.62  thf('112', plain,
% 1.38/1.62      (![X36 : $i, X37 : $i]:
% 1.38/1.62         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.38/1.62  thf('113', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 1.38/1.62      inference('simplify', [status(thm)], ['112'])).
% 1.38/1.62  thf('114', plain,
% 1.38/1.62      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.38/1.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.38/1.62  thf('115', plain,
% 1.38/1.62      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.38/1.62         (~ (zip_tseitin_0 @ X41 @ X42)
% 1.38/1.62          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 1.38/1.62          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.38/1.62  thf('116', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup-', [status(thm)], ['114', '115'])).
% 1.38/1.62  thf('117', plain,
% 1.38/1.62      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.38/1.62      inference('sup-', [status(thm)], ['113', '116'])).
% 1.38/1.62  thf('118', plain,
% 1.38/1.62      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.38/1.62      inference('demod', [status(thm)], ['111', '117'])).
% 1.38/1.62  thf('119', plain, ($false),
% 1.38/1.62      inference('demod', [status(thm)], ['96', '103', '118'])).
% 1.38/1.62  
% 1.38/1.62  % SZS output end Refutation
% 1.38/1.62  
% 1.38/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
