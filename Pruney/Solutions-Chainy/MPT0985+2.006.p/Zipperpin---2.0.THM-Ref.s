%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CPbunCyEQI

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:27 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  191 (1297 expanded)
%              Number of leaves         :   46 ( 410 expanded)
%              Depth                    :   21
%              Number of atoms          : 1341 (20499 expanded)
%              Number of equality atoms :   84 ( 781 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
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
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
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
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
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
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_B
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
    ! [X36: $i] :
      ( ( v1_funct_2 @ X36 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('47',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('49',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','54','60','66'])).

thf('68',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','67'])).

thf('69',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('70',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','72'])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('76',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('80',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','80','81'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('83',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('84',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('86',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','88'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('90',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( v1_funct_2 @ X37 @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('93',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('94',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('95',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('96',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['73','84','89','97'])).

thf('99',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','98','99'])).

thf('101',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','100'])).

thf('102',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('104',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('105',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X36: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('108',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','105'])).

thf('113',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('114',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X1 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ X0 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['110','117'])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
        | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
        | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','118'])).

thf('120',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('121',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('122',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123'])).

thf('125',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_B )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','124'])).

thf('126',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_B )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('129',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('131',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('133',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','98','99'])).

thf('135',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['133','134'])).

thf('136',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','135'])).

thf('137',plain,(
    ! [X36: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('138',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('140',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('141',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('142',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['101','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CPbunCyEQI
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:49:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.12  % Solved by: fo/fo7.sh
% 0.90/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.12  % done 649 iterations in 0.665s
% 0.90/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.12  % SZS output start Refutation
% 0.90/1.12  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.12  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.12  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.12  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.90/1.12  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.12  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.90/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.12  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.90/1.12  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.12  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.12  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.90/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.12  thf(t31_funct_2, conjecture,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.12       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.90/1.12         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.90/1.12           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.90/1.12           ( m1_subset_1 @
% 0.90/1.12             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.90/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.12    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.12        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.12            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.12          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.90/1.12            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.90/1.12              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.90/1.12              ( m1_subset_1 @
% 0.90/1.12                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.90/1.12    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.90/1.12  thf('0', plain,
% 0.90/1.12      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.90/1.12        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.90/1.12        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('1', plain,
% 0.90/1.12      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf('2', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(d9_funct_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.12       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.90/1.12  thf('3', plain,
% 0.90/1.12      (![X15 : $i]:
% 0.90/1.12         (~ (v2_funct_1 @ X15)
% 0.90/1.12          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 0.90/1.12          | ~ (v1_funct_1 @ X15)
% 0.90/1.12          | ~ (v1_relat_1 @ X15))),
% 0.90/1.12      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.90/1.12  thf('4', plain,
% 0.90/1.12      ((~ (v1_relat_1 @ sk_C)
% 0.90/1.12        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.90/1.12        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.12      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.12  thf('5', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(cc1_relset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( v1_relat_1 @ C ) ))).
% 0.90/1.12  thf('6', plain,
% 0.90/1.12      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.90/1.12         ((v1_relat_1 @ X19)
% 0.90/1.12          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.90/1.12      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.12  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.12  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.90/1.12  thf('10', plain,
% 0.90/1.12      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.90/1.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('demod', [status(thm)], ['1', '9'])).
% 0.90/1.12  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.12  thf(dt_k2_funct_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.12       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.90/1.12         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.90/1.12  thf('12', plain,
% 0.90/1.12      (![X16 : $i]:
% 0.90/1.12         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 0.90/1.12          | ~ (v1_funct_1 @ X16)
% 0.90/1.12          | ~ (v1_relat_1 @ X16))),
% 0.90/1.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.12  thf('13', plain,
% 0.90/1.12      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.90/1.12         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf('14', plain,
% 0.90/1.12      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.90/1.12         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.12  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('16', plain,
% 0.90/1.12      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.90/1.12      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.12  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['11', '16'])).
% 0.90/1.12  thf('18', plain,
% 0.90/1.12      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.90/1.12         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf('19', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.90/1.12  thf(d1_funct_2, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.12           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.90/1.12             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.90/1.12         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.12           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.90/1.12             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.90/1.12  thf(zf_stmt_1, axiom,
% 0.90/1.12    (![B:$i,A:$i]:
% 0.90/1.12     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.12       ( zip_tseitin_0 @ B @ A ) ))).
% 0.90/1.12  thf('20', plain,
% 0.90/1.12      (![X28 : $i, X29 : $i]:
% 0.90/1.12         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.12  thf('21', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.90/1.12  thf(zf_stmt_3, axiom,
% 0.90/1.12    (![C:$i,B:$i,A:$i]:
% 0.90/1.12     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.90/1.12       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.90/1.12  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.90/1.12  thf(zf_stmt_5, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.90/1.12         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.12           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.90/1.12             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.90/1.12  thf('22', plain,
% 0.90/1.12      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.90/1.12         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.90/1.12          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.90/1.12          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.12  thf('23', plain,
% 0.90/1.12      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.90/1.12      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.12  thf('24', plain,
% 0.90/1.12      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.90/1.12      inference('sup-', [status(thm)], ['20', '23'])).
% 0.90/1.12  thf('25', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('26', plain,
% 0.90/1.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.90/1.12         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.90/1.12          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.90/1.12          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.90/1.12  thf('27', plain,
% 0.90/1.12      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.90/1.12        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['25', '26'])).
% 0.90/1.12  thf('28', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.12  thf('29', plain,
% 0.90/1.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.12         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.90/1.12          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.12  thf('30', plain,
% 0.90/1.12      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.90/1.12      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.12  thf('31', plain,
% 0.90/1.12      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['27', '30'])).
% 0.90/1.12  thf('32', plain,
% 0.90/1.12      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['24', '31'])).
% 0.90/1.12  thf('33', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.90/1.12  thf(t55_funct_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.12       ( ( v2_funct_1 @ A ) =>
% 0.90/1.12         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.90/1.12           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.12  thf('34', plain,
% 0.90/1.12      (![X17 : $i]:
% 0.90/1.12         (~ (v2_funct_1 @ X17)
% 0.90/1.12          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 0.90/1.12          | ~ (v1_funct_1 @ X17)
% 0.90/1.12          | ~ (v1_relat_1 @ X17))),
% 0.90/1.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.90/1.12  thf('35', plain,
% 0.90/1.12      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.90/1.12        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.12        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.12        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.12      inference('sup+', [status(thm)], ['33', '34'])).
% 0.90/1.12  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.12  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('38', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('39', plain,
% 0.90/1.12      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.90/1.12  thf('40', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(redefinition_k2_relset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.12       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.90/1.12  thf('41', plain,
% 0.90/1.12      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.12         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.90/1.12          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.12  thf('42', plain,
% 0.90/1.12      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.90/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.90/1.12  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('44', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.90/1.12      inference('sup+', [status(thm)], ['42', '43'])).
% 0.90/1.12  thf('45', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['39', '44'])).
% 0.90/1.12  thf(t3_funct_2, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.12       ( ( v1_funct_1 @ A ) & 
% 0.90/1.12         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.90/1.12         ( m1_subset_1 @
% 0.90/1.12           A @ 
% 0.90/1.12           ( k1_zfmisc_1 @
% 0.90/1.12             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.12  thf('46', plain,
% 0.90/1.12      (![X36 : $i]:
% 0.90/1.12         ((v1_funct_2 @ X36 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36))
% 0.90/1.12          | ~ (v1_funct_1 @ X36)
% 0.90/1.12          | ~ (v1_relat_1 @ X36))),
% 0.90/1.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.90/1.12  thf('47', plain,
% 0.90/1.12      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ 
% 0.90/1.12         (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.90/1.12        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.90/1.12        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.12      inference('sup+', [status(thm)], ['45', '46'])).
% 0.90/1.12  thf('48', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.90/1.12  thf('49', plain,
% 0.90/1.12      (![X17 : $i]:
% 0.90/1.12         (~ (v2_funct_1 @ X17)
% 0.90/1.12          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 0.90/1.12          | ~ (v1_funct_1 @ X17)
% 0.90/1.12          | ~ (v1_relat_1 @ X17))),
% 0.90/1.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.90/1.12  thf('50', plain,
% 0.90/1.12      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.90/1.12        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.12        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.12        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.12      inference('sup+', [status(thm)], ['48', '49'])).
% 0.90/1.12  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.12  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('54', plain,
% 0.90/1.12      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.90/1.12  thf('55', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.90/1.12  thf('56', plain,
% 0.90/1.12      (![X16 : $i]:
% 0.90/1.12         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.90/1.12          | ~ (v1_funct_1 @ X16)
% 0.90/1.12          | ~ (v1_relat_1 @ X16))),
% 0.90/1.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.12  thf('57', plain,
% 0.90/1.12      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.90/1.12        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.12        | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.12      inference('sup+', [status(thm)], ['55', '56'])).
% 0.90/1.12  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.12  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('60', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.90/1.12  thf('61', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.90/1.12  thf('62', plain,
% 0.90/1.12      (![X16 : $i]:
% 0.90/1.12         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 0.90/1.12          | ~ (v1_funct_1 @ X16)
% 0.90/1.12          | ~ (v1_relat_1 @ X16))),
% 0.90/1.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.12  thf('63', plain,
% 0.90/1.12      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.90/1.12        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.12        | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.12      inference('sup+', [status(thm)], ['61', '62'])).
% 0.90/1.12  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.12  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('66', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.90/1.12  thf('67', plain,
% 0.90/1.12      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['47', '54', '60', '66'])).
% 0.90/1.12  thf('68', plain,
% 0.90/1.12      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.90/1.12        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup+', [status(thm)], ['32', '67'])).
% 0.90/1.12  thf('69', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.90/1.12  thf('70', plain,
% 0.90/1.12      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.90/1.12         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf('71', plain,
% 0.90/1.12      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.90/1.12         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.12  thf('72', plain,
% 0.90/1.12      ((((sk_B) = (k1_xboole_0)))
% 0.90/1.12         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['68', '71'])).
% 0.90/1.12  thf('73', plain,
% 0.90/1.12      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 0.90/1.12         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.90/1.12      inference('demod', [status(thm)], ['18', '19', '72'])).
% 0.90/1.12  thf('74', plain,
% 0.90/1.12      ((((sk_B) = (k1_xboole_0)))
% 0.90/1.12         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['68', '71'])).
% 0.90/1.12  thf('75', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(cc1_subset_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( v1_xboole_0 @ A ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.90/1.12  thf('76', plain,
% 0.90/1.12      (![X6 : $i, X7 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.90/1.12          | (v1_xboole_0 @ X6)
% 0.90/1.12          | ~ (v1_xboole_0 @ X7))),
% 0.90/1.12      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.90/1.12  thf('77', plain,
% 0.90/1.12      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.90/1.12      inference('sup-', [status(thm)], ['75', '76'])).
% 0.90/1.12  thf('78', plain,
% 0.90/1.12      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 0.90/1.12         | (v1_xboole_0 @ sk_C)))
% 0.90/1.12         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['74', '77'])).
% 0.90/1.12  thf(t113_zfmisc_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.90/1.12       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.90/1.12  thf('79', plain,
% 0.90/1.12      (![X3 : $i, X4 : $i]:
% 0.90/1.12         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.90/1.12  thf('80', plain,
% 0.90/1.12      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.12      inference('simplify', [status(thm)], ['79'])).
% 0.90/1.12  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.90/1.12  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.12  thf('82', plain,
% 0.90/1.12      (((v1_xboole_0 @ sk_C))
% 0.90/1.12         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.90/1.12      inference('demod', [status(thm)], ['78', '80', '81'])).
% 0.90/1.12  thf(l13_xboole_0, axiom,
% 0.90/1.12    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.12  thf('83', plain,
% 0.90/1.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.12  thf('84', plain,
% 0.90/1.12      ((((sk_C) = (k1_xboole_0)))
% 0.90/1.12         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['82', '83'])).
% 0.90/1.12  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.12  thf(fc14_relat_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( v1_xboole_0 @ A ) =>
% 0.90/1.12       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 0.90/1.12         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.90/1.12  thf('86', plain,
% 0.90/1.12      (![X12 : $i]:
% 0.90/1.12         ((v1_xboole_0 @ (k4_relat_1 @ X12)) | ~ (v1_xboole_0 @ X12))),
% 0.90/1.12      inference('cnf', [status(esa)], [fc14_relat_1])).
% 0.90/1.12  thf('87', plain,
% 0.90/1.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.12  thf('88', plain,
% 0.90/1.12      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['86', '87'])).
% 0.90/1.12  thf('89', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['85', '88'])).
% 0.90/1.12  thf(t60_relat_1, axiom,
% 0.90/1.12    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.90/1.12     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.90/1.12  thf('90', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.90/1.12  thf(t4_funct_2, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.12       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.90/1.12         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.90/1.12           ( m1_subset_1 @
% 0.90/1.12             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.90/1.12  thf('91', plain,
% 0.90/1.12      (![X37 : $i, X38 : $i]:
% 0.90/1.12         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 0.90/1.12          | (v1_funct_2 @ X37 @ (k1_relat_1 @ X37) @ X38)
% 0.90/1.12          | ~ (v1_funct_1 @ X37)
% 0.90/1.12          | ~ (v1_relat_1 @ X37))),
% 0.90/1.12      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.90/1.12  thf('92', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.90/1.12          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.12          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.90/1.12          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['90', '91'])).
% 0.90/1.12  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.90/1.12  thf('93', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.90/1.12      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.90/1.12  thf(t45_ordinal1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.90/1.12       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.90/1.12  thf('94', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.12      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.90/1.12  thf('95', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.90/1.12      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.90/1.12  thf('96', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.90/1.12  thf('97', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.90/1.12      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.90/1.12  thf('98', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.90/1.12      inference('demod', [status(thm)], ['73', '84', '89', '97'])).
% 0.90/1.12  thf('99', plain,
% 0.90/1.12      (~
% 0.90/1.12       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.90/1.12       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.90/1.12       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf('100', plain,
% 0.90/1.12      (~
% 0.90/1.12       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.90/1.12      inference('sat_resolution*', [status(thm)], ['17', '98', '99'])).
% 0.90/1.12  thf('101', plain,
% 0.90/1.12      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.90/1.12          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.12      inference('simpl_trail', [status(thm)], ['10', '100'])).
% 0.90/1.12  thf('102', plain,
% 0.90/1.12      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.90/1.12  thf('103', plain,
% 0.90/1.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.12  thf('104', plain,
% 0.90/1.12      (![X3 : $i, X4 : $i]:
% 0.90/1.12         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.90/1.12  thf('105', plain,
% 0.90/1.12      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.90/1.12      inference('simplify', [status(thm)], ['104'])).
% 0.90/1.12  thf('106', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('sup+', [status(thm)], ['103', '105'])).
% 0.90/1.12  thf('107', plain,
% 0.90/1.12      (![X36 : $i]:
% 0.90/1.12         ((m1_subset_1 @ X36 @ 
% 0.90/1.12           (k1_zfmisc_1 @ 
% 0.90/1.12            (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36))))
% 0.90/1.12          | ~ (v1_funct_1 @ X36)
% 0.90/1.12          | ~ (v1_relat_1 @ X36))),
% 0.90/1.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.90/1.12  thf('108', plain,
% 0.90/1.12      (![X28 : $i, X29 : $i]:
% 0.90/1.12         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.12  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.12  thf('110', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.90/1.12      inference('sup+', [status(thm)], ['108', '109'])).
% 0.90/1.12  thf('111', plain,
% 0.90/1.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.12  thf('112', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('sup+', [status(thm)], ['103', '105'])).
% 0.90/1.12  thf('113', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['4', '7', '8'])).
% 0.90/1.12  thf('114', plain,
% 0.90/1.12      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf('115', plain,
% 0.90/1.12      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.90/1.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['113', '114'])).
% 0.90/1.12  thf('116', plain,
% 0.90/1.12      (((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.90/1.12         | ~ (v1_xboole_0 @ sk_B)))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['112', '115'])).
% 0.90/1.12  thf('117', plain,
% 0.90/1.12      ((![X0 : $i]:
% 0.90/1.12          (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ (k1_zfmisc_1 @ X0))
% 0.90/1.12           | ~ (v1_xboole_0 @ X0)
% 0.90/1.12           | ~ (v1_xboole_0 @ sk_B)))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['111', '116'])).
% 0.90/1.12  thf('118', plain,
% 0.90/1.12      ((![X0 : $i, X1 : $i]:
% 0.90/1.12          ((zip_tseitin_0 @ sk_B @ X1)
% 0.90/1.12           | ~ (v1_xboole_0 @ X0)
% 0.90/1.12           | ~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ (k1_zfmisc_1 @ X0))))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['110', '117'])).
% 0.90/1.12  thf('119', plain,
% 0.90/1.12      ((![X0 : $i]:
% 0.90/1.12          (~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.90/1.12           | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.90/1.12           | ~ (v1_xboole_0 @ 
% 0.90/1.12                (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.90/1.12                 (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 0.90/1.12           | (zip_tseitin_0 @ sk_B @ X0)))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['107', '118'])).
% 0.90/1.12  thf('120', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.90/1.12  thf('121', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.90/1.12  thf('122', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['39', '44'])).
% 0.90/1.12  thf('123', plain,
% 0.90/1.12      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.90/1.12  thf('124', plain,
% 0.90/1.12      ((![X0 : $i]:
% 0.90/1.12          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C)))
% 0.90/1.12           | (zip_tseitin_0 @ sk_B @ X0)))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('demod', [status(thm)], ['119', '120', '121', '122', '123'])).
% 0.90/1.12  thf('125', plain,
% 0.90/1.12      ((![X0 : $i]:
% 0.90/1.12          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.12           | ~ (v1_xboole_0 @ sk_B)
% 0.90/1.12           | (zip_tseitin_0 @ sk_B @ X0)))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['106', '124'])).
% 0.90/1.12  thf('126', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.12  thf('127', plain,
% 0.90/1.12      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | (zip_tseitin_0 @ sk_B @ X0)))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('demod', [status(thm)], ['125', '126'])).
% 0.90/1.12  thf('128', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.90/1.12      inference('sup+', [status(thm)], ['108', '109'])).
% 0.90/1.12  thf('129', plain,
% 0.90/1.12      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('clc', [status(thm)], ['127', '128'])).
% 0.90/1.12  thf('130', plain,
% 0.90/1.12      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.90/1.12      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.12  thf('131', plain,
% 0.90/1.12      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['129', '130'])).
% 0.90/1.12  thf('132', plain,
% 0.90/1.12      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['27', '30'])).
% 0.90/1.12  thf('133', plain,
% 0.90/1.12      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 0.90/1.12         <= (~
% 0.90/1.12             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['131', '132'])).
% 0.90/1.12  thf('134', plain,
% 0.90/1.12      (~
% 0.90/1.12       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.90/1.12         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.90/1.12      inference('sat_resolution*', [status(thm)], ['17', '98', '99'])).
% 0.90/1.12  thf('135', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.12      inference('simpl_trail', [status(thm)], ['133', '134'])).
% 0.90/1.12  thf('136', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['102', '135'])).
% 0.90/1.12  thf('137', plain,
% 0.90/1.12      (![X36 : $i]:
% 0.90/1.12         ((m1_subset_1 @ X36 @ 
% 0.90/1.12           (k1_zfmisc_1 @ 
% 0.90/1.12            (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36))))
% 0.90/1.12          | ~ (v1_funct_1 @ X36)
% 0.90/1.12          | ~ (v1_relat_1 @ X36))),
% 0.90/1.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.90/1.12  thf('138', plain,
% 0.90/1.12      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.90/1.12         (k1_zfmisc_1 @ 
% 0.90/1.12          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 0.90/1.12        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.90/1.12        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.12      inference('sup+', [status(thm)], ['136', '137'])).
% 0.90/1.12  thf('139', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.90/1.12      inference('demod', [status(thm)], ['39', '44'])).
% 0.90/1.12  thf('140', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.90/1.12  thf('141', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.90/1.12      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.90/1.12  thf('142', plain,
% 0.90/1.12      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.90/1.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.12      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.90/1.12  thf('143', plain, ($false), inference('demod', [status(thm)], ['101', '142'])).
% 0.90/1.12  
% 0.90/1.12  % SZS output end Refutation
% 0.90/1.12  
% 0.96/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
