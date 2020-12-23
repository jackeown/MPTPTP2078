%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.63rxQKr9f6

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:27 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  233 (1635 expanded)
%              Number of leaves         :   45 ( 515 expanded)
%              Depth                    :   26
%              Number of atoms          : 1595 (23910 expanded)
%              Number of equality atoms :  106 ( 956 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('18',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

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

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('22',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X37: $i] :
      ( ( v1_funct_2 @ X37 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('47',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('49',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('56',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('57',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('62',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('63',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','54','60','66'])).

thf('68',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','67'])).

thf('69',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('70',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','72'])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X5 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('77',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('80',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('82',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('86',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X16 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('98',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X4 ) )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('102',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('103',plain,(
    ! [X2: $i] :
      ( v1_xboole_0 @ ( sk_B @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('105',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('110',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('112',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('116',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X28 ) ) )
      | ( v1_partfun1 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('117',plain,(
    ! [X1: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('118',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('119',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('120',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_partfun1 @ X23 @ X24 )
      | ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','124'])).

thf('126',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( X1
        = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('130',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('131',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','131'])).

thf('133',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31
       != ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('137',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['73','96','101','137'])).

thf('139',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('140',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','138','139'])).

thf('141',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','140'])).

thf('142',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('143',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('144',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('146',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('147',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X5 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['145','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X4 ) )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('163',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('166',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('167',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C ) @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['161','168'])).

thf('170',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('171',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['169','172'])).

thf('174',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','138','139'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference(simpl_trail,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['158','175'])).

thf('177',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['144','176'])).

thf('178',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','177'])).

thf('179',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['142','178'])).

thf('180',plain,(
    ! [X37: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('181',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('183',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('184',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('185',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['181','182','183','184'])).

thf('186',plain,(
    $false ),
    inference(demod,[status(thm)],['141','185'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.63rxQKr9f6
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:19:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 1.15/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.34  % Solved by: fo/fo7.sh
% 1.15/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.34  % done 1010 iterations in 0.876s
% 1.15/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.34  % SZS output start Refutation
% 1.15/1.34  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.15/1.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.15/1.34  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.15/1.34  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.15/1.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.15/1.34  thf(sk_B_type, type, sk_B: $i > $i).
% 1.15/1.34  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.15/1.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.15/1.34  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.15/1.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.15/1.34  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.15/1.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.15/1.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.15/1.34  thf(sk_C_type, type, sk_C: $i).
% 1.15/1.34  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.15/1.34  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.15/1.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.15/1.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.15/1.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.34  thf(t31_funct_2, conjecture,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.34       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.15/1.34         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.15/1.34           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.15/1.34           ( m1_subset_1 @
% 1.15/1.34             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.15/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.34    (~( ![A:$i,B:$i,C:$i]:
% 1.15/1.34        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.34            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.34          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.15/1.34            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.15/1.34              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.15/1.34              ( m1_subset_1 @
% 1.15/1.34                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.15/1.34    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.15/1.34  thf('0', plain,
% 1.15/1.34      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.34        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)
% 1.15/1.34        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('1', plain,
% 1.15/1.34      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 1.15/1.34         <= (~
% 1.15/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.15/1.34      inference('split', [status(esa)], ['0'])).
% 1.15/1.34  thf('2', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(d9_funct_1, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.34       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.15/1.34  thf('3', plain,
% 1.15/1.34      (![X8 : $i]:
% 1.15/1.34         (~ (v2_funct_1 @ X8)
% 1.15/1.34          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 1.15/1.34          | ~ (v1_funct_1 @ X8)
% 1.15/1.34          | ~ (v1_relat_1 @ X8))),
% 1.15/1.34      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.15/1.34  thf('4', plain,
% 1.15/1.34      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.34        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.15/1.34        | ~ (v2_funct_1 @ sk_C))),
% 1.15/1.34      inference('sup-', [status(thm)], ['2', '3'])).
% 1.15/1.34  thf('5', plain,
% 1.15/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(cc1_relset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( v1_relat_1 @ C ) ))).
% 1.15/1.34  thf('6', plain,
% 1.15/1.34      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.15/1.34         ((v1_relat_1 @ X11)
% 1.15/1.34          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.15/1.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.15/1.34  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.15/1.34  thf('10', plain,
% 1.15/1.34      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.15/1.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 1.15/1.34         <= (~
% 1.15/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.15/1.34      inference('demod', [status(thm)], ['1', '9'])).
% 1.15/1.34  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf(dt_k2_funct_1, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.34       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.15/1.34         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.15/1.34  thf('12', plain,
% 1.15/1.34      (![X9 : $i]:
% 1.15/1.34         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.15/1.34          | ~ (v1_funct_1 @ X9)
% 1.15/1.34          | ~ (v1_relat_1 @ X9))),
% 1.15/1.34      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.34  thf('13', plain,
% 1.15/1.34      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.34         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.15/1.34      inference('split', [status(esa)], ['0'])).
% 1.15/1.34  thf('14', plain,
% 1.15/1.34      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.15/1.34         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.15/1.34      inference('sup-', [status(thm)], ['12', '13'])).
% 1.15/1.34  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('16', plain,
% 1.15/1.34      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.15/1.34      inference('demod', [status(thm)], ['14', '15'])).
% 1.15/1.34  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['11', '16'])).
% 1.15/1.34  thf('18', plain,
% 1.15/1.34      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('split', [status(esa)], ['0'])).
% 1.15/1.34  thf('19', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.15/1.34  thf(d1_funct_2, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.15/1.34           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.15/1.34             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.15/1.34         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.15/1.34           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.15/1.34             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.15/1.34  thf(zf_stmt_1, axiom,
% 1.15/1.34    (![B:$i,A:$i]:
% 1.15/1.34     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.15/1.34       ( zip_tseitin_0 @ B @ A ) ))).
% 1.15/1.34  thf('20', plain,
% 1.15/1.34      (![X29 : $i, X30 : $i]:
% 1.15/1.34         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.15/1.34  thf('21', plain,
% 1.15/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.15/1.34  thf(zf_stmt_3, axiom,
% 1.15/1.34    (![C:$i,B:$i,A:$i]:
% 1.15/1.34     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.15/1.34       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.15/1.34  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.15/1.34  thf(zf_stmt_5, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.15/1.34         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.15/1.34           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.15/1.34             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.15/1.34  thf('22', plain,
% 1.15/1.34      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.15/1.34         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.15/1.34          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.15/1.34          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.15/1.34  thf('23', plain,
% 1.15/1.34      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.15/1.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['21', '22'])).
% 1.15/1.34  thf('24', plain,
% 1.15/1.34      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['20', '23'])).
% 1.15/1.34  thf('25', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('26', plain,
% 1.15/1.34      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.15/1.34         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.15/1.34          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.15/1.34          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.15/1.34  thf('27', plain,
% 1.15/1.34      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.15/1.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['25', '26'])).
% 1.15/1.34  thf('28', plain,
% 1.15/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(redefinition_k1_relset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.15/1.34  thf('29', plain,
% 1.15/1.34      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.15/1.34         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.15/1.34          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.15/1.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.15/1.34  thf('30', plain,
% 1.15/1.34      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.15/1.34      inference('sup-', [status(thm)], ['28', '29'])).
% 1.15/1.34  thf('31', plain,
% 1.15/1.34      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.15/1.34        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.15/1.34      inference('demod', [status(thm)], ['27', '30'])).
% 1.15/1.34  thf('32', plain,
% 1.15/1.34      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['24', '31'])).
% 1.15/1.34  thf('33', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.15/1.34  thf(t55_funct_1, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.34       ( ( v2_funct_1 @ A ) =>
% 1.15/1.34         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.15/1.34           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.15/1.34  thf('34', plain,
% 1.15/1.34      (![X10 : $i]:
% 1.15/1.34         (~ (v2_funct_1 @ X10)
% 1.15/1.34          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.15/1.34          | ~ (v1_funct_1 @ X10)
% 1.15/1.34          | ~ (v1_relat_1 @ X10))),
% 1.15/1.34      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.15/1.34  thf('35', plain,
% 1.15/1.34      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.15/1.34        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.34        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.34        | ~ (v2_funct_1 @ sk_C))),
% 1.15/1.34      inference('sup+', [status(thm)], ['33', '34'])).
% 1.15/1.34  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('38', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('39', plain,
% 1.15/1.34      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.15/1.34      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.15/1.34  thf('40', plain,
% 1.15/1.34      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf(redefinition_k2_relset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.15/1.34  thf('41', plain,
% 1.15/1.34      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.15/1.34         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.15/1.34          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.15/1.34      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.15/1.34  thf('42', plain,
% 1.15/1.34      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.15/1.34      inference('sup-', [status(thm)], ['40', '41'])).
% 1.15/1.34  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_B_1))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('44', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['42', '43'])).
% 1.15/1.34  thf('45', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.15/1.34      inference('demod', [status(thm)], ['39', '44'])).
% 1.15/1.34  thf(t3_funct_2, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.34       ( ( v1_funct_1 @ A ) & 
% 1.15/1.34         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.15/1.34         ( m1_subset_1 @
% 1.15/1.34           A @ 
% 1.15/1.34           ( k1_zfmisc_1 @
% 1.15/1.34             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.15/1.34  thf('46', plain,
% 1.15/1.34      (![X37 : $i]:
% 1.15/1.34         ((v1_funct_2 @ X37 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))
% 1.15/1.34          | ~ (v1_funct_1 @ X37)
% 1.15/1.34          | ~ (v1_relat_1 @ X37))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.15/1.34  thf('47', plain,
% 1.15/1.34      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ 
% 1.15/1.34         (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.15/1.34        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.15/1.34        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['45', '46'])).
% 1.15/1.34  thf('48', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.15/1.34  thf('49', plain,
% 1.15/1.34      (![X10 : $i]:
% 1.15/1.34         (~ (v2_funct_1 @ X10)
% 1.15/1.34          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 1.15/1.34          | ~ (v1_funct_1 @ X10)
% 1.15/1.34          | ~ (v1_relat_1 @ X10))),
% 1.15/1.34      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.15/1.34  thf('50', plain,
% 1.15/1.34      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.15/1.34        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.34        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.34        | ~ (v2_funct_1 @ sk_C))),
% 1.15/1.34      inference('sup+', [status(thm)], ['48', '49'])).
% 1.15/1.34  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('54', plain,
% 1.15/1.34      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.15/1.34      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 1.15/1.34  thf('55', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.15/1.34  thf('56', plain,
% 1.15/1.34      (![X9 : $i]:
% 1.15/1.34         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.15/1.34          | ~ (v1_funct_1 @ X9)
% 1.15/1.34          | ~ (v1_relat_1 @ X9))),
% 1.15/1.34      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.34  thf('57', plain,
% 1.15/1.34      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.15/1.34        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.34        | ~ (v1_funct_1 @ sk_C))),
% 1.15/1.34      inference('sup+', [status(thm)], ['55', '56'])).
% 1.15/1.34  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('60', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.15/1.34  thf('61', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.15/1.34  thf('62', plain,
% 1.15/1.34      (![X9 : $i]:
% 1.15/1.34         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.15/1.34          | ~ (v1_funct_1 @ X9)
% 1.15/1.34          | ~ (v1_relat_1 @ X9))),
% 1.15/1.34      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.34  thf('63', plain,
% 1.15/1.34      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 1.15/1.34        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.34        | ~ (v1_funct_1 @ sk_C))),
% 1.15/1.34      inference('sup+', [status(thm)], ['61', '62'])).
% 1.15/1.34  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('66', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.15/1.34  thf('67', plain,
% 1.15/1.34      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ (k1_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['47', '54', '60', '66'])).
% 1.15/1.34  thf('68', plain,
% 1.15/1.34      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A)
% 1.15/1.34        | ((sk_B_1) = (k1_xboole_0)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['32', '67'])).
% 1.15/1.34  thf('69', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.15/1.34  thf('70', plain,
% 1.15/1.34      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('split', [status(esa)], ['0'])).
% 1.15/1.34  thf('71', plain,
% 1.15/1.34      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['69', '70'])).
% 1.15/1.34  thf('72', plain,
% 1.15/1.34      ((((sk_B_1) = (k1_xboole_0)))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['68', '71'])).
% 1.15/1.34  thf('73', plain,
% 1.15/1.34      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('demod', [status(thm)], ['18', '19', '72'])).
% 1.15/1.34  thf('74', plain,
% 1.15/1.34      ((((sk_B_1) = (k1_xboole_0)))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['68', '71'])).
% 1.15/1.34  thf('75', plain,
% 1.15/1.34      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.15/1.34      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 1.15/1.34  thf(t65_relat_1, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( v1_relat_1 @ A ) =>
% 1.15/1.34       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 1.15/1.34         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 1.15/1.34  thf('76', plain,
% 1.15/1.34      (![X5 : $i]:
% 1.15/1.34         (((k1_relat_1 @ X5) != (k1_xboole_0))
% 1.15/1.34          | ((k2_relat_1 @ X5) = (k1_xboole_0))
% 1.15/1.34          | ~ (v1_relat_1 @ X5))),
% 1.15/1.34      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.15/1.34  thf('77', plain,
% 1.15/1.34      ((((k2_relat_1 @ sk_C) != (k1_xboole_0))
% 1.15/1.34        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.15/1.34        | ((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_xboole_0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['75', '76'])).
% 1.15/1.34  thf('78', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.15/1.34  thf('79', plain,
% 1.15/1.34      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.15/1.34      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 1.15/1.34  thf('80', plain,
% 1.15/1.34      ((((k2_relat_1 @ sk_C) != (k1_xboole_0))
% 1.15/1.34        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.15/1.34      inference('demod', [status(thm)], ['77', '78', '79'])).
% 1.15/1.34  thf('81', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['42', '43'])).
% 1.15/1.34  thf('82', plain,
% 1.15/1.34      ((((sk_B_1) != (k1_xboole_0)) | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.15/1.34      inference('demod', [status(thm)], ['80', '81'])).
% 1.15/1.34  thf('83', plain,
% 1.15/1.34      (((((k1_xboole_0) != (k1_xboole_0))
% 1.15/1.34         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['74', '82'])).
% 1.15/1.34  thf('84', plain,
% 1.15/1.34      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('simplify', [status(thm)], ['83'])).
% 1.15/1.34  thf('85', plain,
% 1.15/1.34      (![X37 : $i]:
% 1.15/1.34         ((m1_subset_1 @ X37 @ 
% 1.15/1.34           (k1_zfmisc_1 @ 
% 1.15/1.34            (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))))
% 1.15/1.34          | ~ (v1_funct_1 @ X37)
% 1.15/1.34          | ~ (v1_relat_1 @ X37))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.15/1.34  thf(cc3_relset_1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( v1_xboole_0 @ A ) =>
% 1.15/1.34       ( ![C:$i]:
% 1.15/1.34         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34           ( v1_xboole_0 @ C ) ) ) ))).
% 1.15/1.34  thf('86', plain,
% 1.15/1.34      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X14)
% 1.15/1.34          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X16)))
% 1.15/1.34          | (v1_xboole_0 @ X15))),
% 1.15/1.34      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.15/1.34  thf('87', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X0)
% 1.15/1.34          | ~ (v1_funct_1 @ X0)
% 1.15/1.34          | (v1_xboole_0 @ X0)
% 1.15/1.34          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['85', '86'])).
% 1.15/1.34  thf('88', plain,
% 1.15/1.34      (((~ (v1_xboole_0 @ k1_xboole_0)
% 1.15/1.34         | (v1_xboole_0 @ sk_C)
% 1.15/1.34         | ~ (v1_funct_1 @ sk_C)
% 1.15/1.34         | ~ (v1_relat_1 @ sk_C)))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['84', '87'])).
% 1.15/1.34  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.15/1.34  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.34  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf('92', plain,
% 1.15/1.34      (((v1_xboole_0 @ sk_C))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 1.15/1.34  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.34  thf(t8_boole, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.15/1.34  thf('94', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t8_boole])).
% 1.15/1.34  thf('95', plain,
% 1.15/1.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['93', '94'])).
% 1.15/1.34  thf('96', plain,
% 1.15/1.34      ((((k1_xboole_0) = (sk_C)))
% 1.15/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['92', '95'])).
% 1.15/1.34  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.34  thf(fc14_relat_1, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ( v1_xboole_0 @ A ) =>
% 1.15/1.34       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 1.15/1.34         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 1.15/1.34  thf('98', plain,
% 1.15/1.34      (![X4 : $i]: ((v1_xboole_0 @ (k4_relat_1 @ X4)) | ~ (v1_xboole_0 @ X4))),
% 1.15/1.34      inference('cnf', [status(esa)], [fc14_relat_1])).
% 1.15/1.34  thf('99', plain,
% 1.15/1.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['93', '94'])).
% 1.15/1.34  thf('100', plain,
% 1.15/1.34      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k4_relat_1 @ X0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['98', '99'])).
% 1.15/1.34  thf('101', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['97', '100'])).
% 1.15/1.34  thf(rc2_subset_1, axiom,
% 1.15/1.34    (![A:$i]:
% 1.15/1.34     ( ?[B:$i]:
% 1.15/1.34       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.15/1.34  thf('102', plain,
% 1.15/1.34      (![X2 : $i]: (m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ X2))),
% 1.15/1.34      inference('cnf', [status(esa)], [rc2_subset_1])).
% 1.15/1.34  thf('103', plain, (![X2 : $i]: (v1_xboole_0 @ (sk_B @ X2))),
% 1.15/1.34      inference('cnf', [status(esa)], [rc2_subset_1])).
% 1.15/1.34  thf('104', plain,
% 1.15/1.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['93', '94'])).
% 1.15/1.34  thf('105', plain, (![X0 : $i]: ((k1_xboole_0) = (sk_B @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['103', '104'])).
% 1.15/1.34  thf('106', plain,
% 1.15/1.34      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 1.15/1.34      inference('demod', [status(thm)], ['102', '105'])).
% 1.15/1.34  thf('107', plain,
% 1.15/1.34      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.15/1.34         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.15/1.34          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.15/1.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.15/1.34  thf('108', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['106', '107'])).
% 1.15/1.34  thf('109', plain,
% 1.15/1.34      (![X29 : $i, X30 : $i]:
% 1.15/1.34         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.15/1.34  thf('110', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 1.15/1.34      inference('simplify', [status(thm)], ['109'])).
% 1.15/1.34  thf('111', plain,
% 1.15/1.34      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 1.15/1.34      inference('demod', [status(thm)], ['102', '105'])).
% 1.15/1.34  thf('112', plain,
% 1.15/1.34      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.15/1.34         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.15/1.34          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.15/1.34          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.15/1.34  thf('113', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['111', '112'])).
% 1.15/1.34  thf('114', plain,
% 1.15/1.34      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.15/1.34      inference('sup-', [status(thm)], ['110', '113'])).
% 1.15/1.34  thf('115', plain,
% 1.15/1.34      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 1.15/1.34      inference('demod', [status(thm)], ['102', '105'])).
% 1.15/1.34  thf(cc1_partfun1, axiom,
% 1.15/1.34    (![A:$i,B:$i]:
% 1.15/1.34     ( ( v1_xboole_0 @ A ) =>
% 1.15/1.34       ( ![C:$i]:
% 1.15/1.34         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34           ( v1_partfun1 @ C @ A ) ) ) ))).
% 1.15/1.34  thf('116', plain,
% 1.15/1.34      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X26)
% 1.15/1.34          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X28)))
% 1.15/1.34          | (v1_partfun1 @ X27 @ X26))),
% 1.15/1.34      inference('cnf', [status(esa)], [cc1_partfun1])).
% 1.15/1.34  thf('117', plain,
% 1.15/1.34      (![X1 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['115', '116'])).
% 1.15/1.34  thf(cc1_funct_1, axiom,
% 1.15/1.34    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 1.15/1.34  thf('118', plain, (![X6 : $i]: ((v1_funct_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 1.15/1.34      inference('cnf', [status(esa)], [cc1_funct_1])).
% 1.15/1.34  thf('119', plain,
% 1.15/1.34      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 1.15/1.34      inference('demod', [status(thm)], ['102', '105'])).
% 1.15/1.34  thf(cc1_funct_2, axiom,
% 1.15/1.34    (![A:$i,B:$i,C:$i]:
% 1.15/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.34       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 1.15/1.34         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 1.15/1.34  thf('120', plain,
% 1.15/1.34      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.15/1.34         (~ (v1_funct_1 @ X23)
% 1.15/1.34          | ~ (v1_partfun1 @ X23 @ X24)
% 1.15/1.34          | (v1_funct_2 @ X23 @ X24 @ X25)
% 1.15/1.34          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.15/1.34      inference('cnf', [status(esa)], [cc1_funct_2])).
% 1.15/1.34  thf('121', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 1.15/1.34          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 1.15/1.34          | ~ (v1_funct_1 @ k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['119', '120'])).
% 1.15/1.34  thf('122', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.15/1.34          | ~ (v1_partfun1 @ k1_xboole_0 @ X0)
% 1.15/1.34          | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['118', '121'])).
% 1.15/1.34  thf('123', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.34  thf('124', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_partfun1 @ k1_xboole_0 @ X0)
% 1.15/1.34          | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('demod', [status(thm)], ['122', '123'])).
% 1.15/1.34  thf('125', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X0) | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['117', '124'])).
% 1.15/1.34  thf('126', plain,
% 1.15/1.34      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.15/1.34         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.15/1.34          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.15/1.34          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.15/1.34  thf('127', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X1)
% 1.15/1.34          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.15/1.34          | ((X1) = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['125', '126'])).
% 1.15/1.34  thf('128', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))
% 1.15/1.34          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['114', '127'])).
% 1.15/1.34  thf('129', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['106', '107'])).
% 1.15/1.34  thf('130', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.34  thf('131', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.15/1.34      inference('demod', [status(thm)], ['128', '129', '130'])).
% 1.15/1.34  thf('132', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.34      inference('demod', [status(thm)], ['108', '131'])).
% 1.15/1.34  thf('133', plain,
% 1.15/1.34      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.15/1.34         (((X31) != (k1_relset_1 @ X31 @ X32 @ X33))
% 1.15/1.34          | (v1_funct_2 @ X33 @ X31 @ X32)
% 1.15/1.34          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.15/1.34  thf('134', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (((X1) != (k1_xboole_0))
% 1.15/1.34          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.15/1.34          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.15/1.34      inference('sup-', [status(thm)], ['132', '133'])).
% 1.15/1.34  thf('135', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.15/1.34          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.34      inference('simplify', [status(thm)], ['134'])).
% 1.15/1.34  thf('136', plain,
% 1.15/1.34      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.15/1.34      inference('sup-', [status(thm)], ['110', '113'])).
% 1.15/1.34  thf('137', plain,
% 1.15/1.34      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.15/1.34      inference('simplify_reflect+', [status(thm)], ['135', '136'])).
% 1.15/1.34  thf('138', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))),
% 1.15/1.34      inference('demod', [status(thm)], ['73', '96', '101', '137'])).
% 1.15/1.34  thf('139', plain,
% 1.15/1.34      (~
% 1.15/1.34       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 1.15/1.34       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)) | 
% 1.15/1.34       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.34      inference('split', [status(esa)], ['0'])).
% 1.15/1.34  thf('140', plain,
% 1.15/1.34      (~
% 1.15/1.34       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 1.15/1.34      inference('sat_resolution*', [status(thm)], ['17', '138', '139'])).
% 1.15/1.34  thf('141', plain,
% 1.15/1.34      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.15/1.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('simpl_trail', [status(thm)], ['10', '140'])).
% 1.15/1.34  thf('142', plain,
% 1.15/1.34      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.15/1.34      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 1.15/1.34  thf('143', plain,
% 1.15/1.34      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.15/1.34        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.15/1.34      inference('demod', [status(thm)], ['27', '30'])).
% 1.15/1.34  thf('144', plain,
% 1.15/1.34      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.15/1.34        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.15/1.34      inference('sup-', [status(thm)], ['21', '22'])).
% 1.15/1.34  thf('145', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['42', '43'])).
% 1.15/1.34  thf('146', plain,
% 1.15/1.34      (![X29 : $i, X30 : $i]:
% 1.15/1.34         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.15/1.34  thf('147', plain,
% 1.15/1.34      (![X5 : $i]:
% 1.15/1.34         (((k2_relat_1 @ X5) != (k1_xboole_0))
% 1.15/1.34          | ((k1_relat_1 @ X5) = (k1_xboole_0))
% 1.15/1.34          | ~ (v1_relat_1 @ X5))),
% 1.15/1.34      inference('cnf', [status(esa)], [t65_relat_1])).
% 1.15/1.34  thf('148', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         (((k2_relat_1 @ X1) != (X0))
% 1.15/1.34          | (zip_tseitin_0 @ X0 @ X2)
% 1.15/1.34          | ~ (v1_relat_1 @ X1)
% 1.15/1.34          | ((k1_relat_1 @ X1) = (k1_xboole_0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['146', '147'])).
% 1.15/1.34  thf('149', plain,
% 1.15/1.34      (![X1 : $i, X2 : $i]:
% 1.15/1.34         (((k1_relat_1 @ X1) = (k1_xboole_0))
% 1.15/1.34          | ~ (v1_relat_1 @ X1)
% 1.15/1.34          | (zip_tseitin_0 @ (k2_relat_1 @ X1) @ X2))),
% 1.15/1.34      inference('simplify', [status(thm)], ['148'])).
% 1.15/1.34  thf('150', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 1.15/1.34          | ~ (v1_relat_1 @ sk_C)
% 1.15/1.34          | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['145', '149'])).
% 1.15/1.34  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf('152', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         ((zip_tseitin_0 @ sk_B_1 @ X0) | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.15/1.34      inference('demod', [status(thm)], ['150', '151'])).
% 1.15/1.34  thf('153', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (~ (v1_relat_1 @ X0)
% 1.15/1.34          | ~ (v1_funct_1 @ X0)
% 1.15/1.34          | (v1_xboole_0 @ X0)
% 1.15/1.34          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 1.15/1.34      inference('sup-', [status(thm)], ['85', '86'])).
% 1.15/1.34  thf('154', plain,
% 1.15/1.34      (![X0 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.15/1.34          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 1.15/1.34          | (v1_xboole_0 @ sk_C)
% 1.15/1.34          | ~ (v1_funct_1 @ sk_C)
% 1.15/1.34          | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.34      inference('sup-', [status(thm)], ['152', '153'])).
% 1.15/1.34  thf('155', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.34  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.34  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.15/1.34  thf('158', plain,
% 1.15/1.34      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 1.15/1.34  thf('159', plain,
% 1.15/1.34      (![X4 : $i]: ((v1_xboole_0 @ (k4_relat_1 @ X4)) | ~ (v1_xboole_0 @ X4))),
% 1.15/1.34      inference('cnf', [status(esa)], [fc14_relat_1])).
% 1.15/1.34  thf('160', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.15/1.34      inference('cnf', [status(esa)], [t8_boole])).
% 1.15/1.34  thf('161', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ X0)
% 1.15/1.34          | ((k4_relat_1 @ X0) = (X1))
% 1.15/1.34          | ~ (v1_xboole_0 @ X1))),
% 1.15/1.34      inference('sup-', [status(thm)], ['159', '160'])).
% 1.15/1.34  thf('162', plain,
% 1.15/1.34      (![X29 : $i, X30 : $i]:
% 1.15/1.34         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.15/1.34  thf('163', plain,
% 1.15/1.34      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 1.15/1.34      inference('demod', [status(thm)], ['102', '105'])).
% 1.15/1.34  thf('164', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.34         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.15/1.34      inference('sup+', [status(thm)], ['162', '163'])).
% 1.15/1.34  thf('165', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.15/1.34  thf('166', plain,
% 1.15/1.34      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 1.15/1.34         <= (~
% 1.15/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.15/1.34      inference('split', [status(esa)], ['0'])).
% 1.15/1.34  thf('167', plain,
% 1.15/1.34      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.15/1.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 1.15/1.34         <= (~
% 1.15/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.15/1.34      inference('sup-', [status(thm)], ['165', '166'])).
% 1.15/1.34  thf('168', plain,
% 1.15/1.34      ((![X0 : $i]: (zip_tseitin_0 @ (k4_relat_1 @ sk_C) @ X0))
% 1.15/1.34         <= (~
% 1.15/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.15/1.34      inference('sup-', [status(thm)], ['164', '167'])).
% 1.15/1.34  thf('169', plain,
% 1.15/1.34      ((![X0 : $i, X1 : $i]:
% 1.15/1.34          ((zip_tseitin_0 @ X0 @ X1)
% 1.15/1.34           | ~ (v1_xboole_0 @ X0)
% 1.15/1.34           | ~ (v1_xboole_0 @ sk_C)))
% 1.15/1.34         <= (~
% 1.15/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.15/1.34      inference('sup+', [status(thm)], ['161', '168'])).
% 1.15/1.34  thf('170', plain,
% 1.15/1.34      (![X29 : $i, X30 : $i]:
% 1.15/1.34         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.15/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.15/1.34  thf('171', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.15/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.15/1.34  thf('172', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.15/1.34      inference('sup+', [status(thm)], ['170', '171'])).
% 1.15/1.34  thf('173', plain,
% 1.15/1.34      ((![X0 : $i, X1 : $i]:
% 1.15/1.34          (~ (v1_xboole_0 @ sk_C) | (zip_tseitin_0 @ X0 @ X1)))
% 1.15/1.34         <= (~
% 1.15/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 1.15/1.34      inference('clc', [status(thm)], ['169', '172'])).
% 1.15/1.34  thf('174', plain,
% 1.15/1.34      (~
% 1.15/1.34       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.34         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 1.15/1.34      inference('sat_resolution*', [status(thm)], ['17', '138', '139'])).
% 1.15/1.34  thf('175', plain,
% 1.15/1.34      (![X0 : $i, X1 : $i]:
% 1.15/1.34         (~ (v1_xboole_0 @ sk_C) | (zip_tseitin_0 @ X0 @ X1))),
% 1.15/1.34      inference('simpl_trail', [status(thm)], ['173', '174'])).
% 1.15/1.34  thf('176', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 1.15/1.34      inference('clc', [status(thm)], ['158', '175'])).
% 1.15/1.34  thf('177', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 1.15/1.34      inference('demod', [status(thm)], ['144', '176'])).
% 1.15/1.34  thf('178', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['143', '177'])).
% 1.15/1.34  thf('179', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.15/1.34      inference('demod', [status(thm)], ['142', '178'])).
% 1.15/1.34  thf('180', plain,
% 1.15/1.34      (![X37 : $i]:
% 1.15/1.34         ((m1_subset_1 @ X37 @ 
% 1.15/1.34           (k1_zfmisc_1 @ 
% 1.15/1.34            (k2_zfmisc_1 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37))))
% 1.15/1.34          | ~ (v1_funct_1 @ X37)
% 1.15/1.34          | ~ (v1_relat_1 @ X37))),
% 1.15/1.34      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.15/1.34  thf('181', plain,
% 1.15/1.34      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.15/1.34         (k1_zfmisc_1 @ 
% 1.15/1.34          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 1.15/1.34        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.15/1.34        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 1.15/1.34      inference('sup+', [status(thm)], ['179', '180'])).
% 1.15/1.34  thf('182', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.15/1.34      inference('demod', [status(thm)], ['39', '44'])).
% 1.15/1.34  thf('183', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.15/1.34  thf('184', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 1.15/1.34      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.15/1.34  thf('185', plain,
% 1.15/1.34      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.15/1.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 1.15/1.34      inference('demod', [status(thm)], ['181', '182', '183', '184'])).
% 1.15/1.34  thf('186', plain, ($false), inference('demod', [status(thm)], ['141', '185'])).
% 1.15/1.34  
% 1.15/1.34  % SZS output end Refutation
% 1.15/1.34  
% 1.15/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
