%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sdlQGHKUPD

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:28 EST 2020

% Result     : Theorem 14.29s
% Output     : Refutation 14.29s
% Verified   : 
% Statistics : Number of formulae       :  269 (4454 expanded)
%              Number of leaves         :   48 (1370 expanded)
%              Depth                    :   33
%              Number of atoms          : 1790 (66702 expanded)
%              Number of equality atoms :  106 (2515 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
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
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_funct_1 @ X24 )
        = ( k4_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
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
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    inference(demod,[status(thm)],['6','7','8'])).

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
    ! [X42: $i,X43: $i] :
      ( ( zip_tseitin_0 @ X42 @ X43 )
      | ( X42 = k1_xboole_0 ) ) ),
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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( zip_tseitin_0 @ X47 @ X48 )
      | ( zip_tseitin_1 @ X49 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_2 @ X46 @ X44 @ X45 )
      | ( X44
        = ( k1_relset_1 @ X44 @ X45 @ X46 ) )
      | ~ ( zip_tseitin_1 @ X46 @ X45 @ X44 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
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
    inference(demod,[status(thm)],['6','7','8'])).

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
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relat_1 @ X30 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
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
    inference('sup-',[status(thm)],['2','3'])).

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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
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
    ! [X50: $i] :
      ( ( v1_funct_2 @ X50 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('47',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('49',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k1_relat_1 @ X30 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
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
    inference('sup-',[status(thm)],['2','3'])).

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
    inference(demod,[status(thm)],['6','7','8'])).

thf('56',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('57',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('62',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('63',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

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
    inference(demod,[status(thm)],['6','7','8'])).

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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('75',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('77',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('85',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('86',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('87',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( r1_tarski @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['82','84','89'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('91',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('92',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','88'])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('94',plain,(
    ! [X19: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X19 ) )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('95',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','92','97'])).

thf('99',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('100',plain,(
    ! [X42: $i,X43: $i] :
      ( ( zip_tseitin_0 @ X42 @ X43 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('106',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('110',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ k1_xboole_0 @ sk_A @ X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('113',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('114',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','92','97'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_funct_2 @ X1 @ X0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,
    ( ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','88'])).

thf('119',plain,
    ( ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_A @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','120'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('122',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('123',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( zip_tseitin_0 @ X47 @ X48 )
      | ( zip_tseitin_1 @ X49 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ k1_xboole_0 @ sk_A @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_1 @ X0 @ sk_A @ X1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['99','125'])).

thf('127',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('128',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44
       != ( k1_relset_1 @ X44 @ X45 @ X46 ) )
      | ( v1_funct_2 @ X46 @ X44 @ X45 )
      | ~ ( zip_tseitin_1 @ X46 @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','88'])).

thf('135',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('136',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B_1 @ k1_xboole_0 )
      = sk_B_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('139',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('140',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('142',plain,(
    ! [X22: $i] :
      ( ( v1_funct_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('143',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('144',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('145',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_funct_1 @ X24 )
        = ( k4_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('147',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','88'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('149',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('150',plain,(
    ! [X23: $i] :
      ( ( v2_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X22: $i] :
      ( ( v1_funct_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['148','154'])).

thf('156',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['147','155'])).

thf('157',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','156'])).

thf('158',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','88'])).

thf('159',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','96'])).

thf('161',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X30: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k1_relat_1 @ X30 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('163',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['143','144'])).

thf('165',plain,(
    ! [X22: $i] :
      ( ( v1_funct_1 @ X22 )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('166',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('167',plain,(
    ! [X25: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('168',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['143','144'])).

thf('170',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_funct_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['165','170'])).

thf('172',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','88'])).

thf('173',plain,(
    v1_funct_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','96'])).

thf('175',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['148','154'])).

thf('177',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['163','164','175','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['141','177'])).

thf('179',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('180',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138','178','179'])).

thf('181',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['133','134','180'])).

thf('182',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['98','181'])).

thf('183',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('184',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','182','183'])).

thf('185',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','184'])).

thf('186',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('188',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('189',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('192',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','88'])).

thf('194',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['187','194'])).

thf('196',plain,(
    ! [X19: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X19 ) )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('197',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('198',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('199',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('202',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['197','202'])).

thf('204',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['196','203'])).

thf('205',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B_1 @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['195','204'])).

thf('206',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('207',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('209',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','182','183'])).

thf('211',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['209','210'])).

thf('212',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','211'])).

thf('213',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('214',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('216',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('217',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('218',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['214','215','216','217'])).

thf('219',plain,(
    $false ),
    inference(demod,[status(thm)],['185','218'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sdlQGHKUPD
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:46:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 14.29/14.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 14.29/14.51  % Solved by: fo/fo7.sh
% 14.29/14.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.29/14.51  % done 14313 iterations in 14.062s
% 14.29/14.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 14.29/14.51  % SZS output start Refutation
% 14.29/14.51  thf(sk_B_type, type, sk_B: $i > $i).
% 14.29/14.51  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 14.29/14.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.29/14.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.29/14.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 14.29/14.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.29/14.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 14.29/14.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 14.29/14.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 14.29/14.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 14.29/14.51  thf(sk_C_type, type, sk_C: $i).
% 14.29/14.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 14.29/14.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 14.29/14.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 14.29/14.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 14.29/14.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 14.29/14.51  thf(sk_A_type, type, sk_A: $i).
% 14.29/14.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 14.29/14.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.29/14.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.29/14.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.29/14.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.29/14.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 14.29/14.51  thf(t31_funct_2, conjecture,
% 14.29/14.51    (![A:$i,B:$i,C:$i]:
% 14.29/14.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 14.29/14.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.29/14.51       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 14.29/14.51         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 14.29/14.51           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 14.29/14.51           ( m1_subset_1 @
% 14.29/14.51             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 14.29/14.51  thf(zf_stmt_0, negated_conjecture,
% 14.29/14.51    (~( ![A:$i,B:$i,C:$i]:
% 14.29/14.51        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 14.29/14.51            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.29/14.51          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 14.29/14.51            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 14.29/14.51              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 14.29/14.51              ( m1_subset_1 @
% 14.29/14.51                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 14.29/14.51    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 14.29/14.51  thf('0', plain,
% 14.29/14.51      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 14.29/14.51        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)
% 14.29/14.51        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('1', plain,
% 14.29/14.51      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 14.29/14.51         <= (~
% 14.29/14.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 14.29/14.51      inference('split', [status(esa)], ['0'])).
% 14.29/14.51  thf('2', plain,
% 14.29/14.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf(cc1_relset_1, axiom,
% 14.29/14.51    (![A:$i,B:$i,C:$i]:
% 14.29/14.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.29/14.51       ( v1_relat_1 @ C ) ))).
% 14.29/14.51  thf('3', plain,
% 14.29/14.51      (![X33 : $i, X34 : $i, X35 : $i]:
% 14.29/14.51         ((v1_relat_1 @ X33)
% 14.29/14.51          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 14.29/14.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 14.29/14.51  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 14.29/14.51      inference('sup-', [status(thm)], ['2', '3'])).
% 14.29/14.51  thf(d9_funct_1, axiom,
% 14.29/14.51    (![A:$i]:
% 14.29/14.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.29/14.51       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 14.29/14.51  thf('5', plain,
% 14.29/14.51      (![X24 : $i]:
% 14.29/14.51         (~ (v2_funct_1 @ X24)
% 14.29/14.51          | ((k2_funct_1 @ X24) = (k4_relat_1 @ X24))
% 14.29/14.51          | ~ (v1_funct_1 @ X24)
% 14.29/14.51          | ~ (v1_relat_1 @ X24))),
% 14.29/14.51      inference('cnf', [status(esa)], [d9_funct_1])).
% 14.29/14.51  thf('6', plain,
% 14.29/14.51      ((~ (v1_funct_1 @ sk_C)
% 14.29/14.51        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 14.29/14.51        | ~ (v2_funct_1 @ sk_C))),
% 14.29/14.51      inference('sup-', [status(thm)], ['4', '5'])).
% 14.29/14.51  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.29/14.51  thf('10', plain,
% 14.29/14.51      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 14.29/14.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 14.29/14.51         <= (~
% 14.29/14.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 14.29/14.51      inference('demod', [status(thm)], ['1', '9'])).
% 14.29/14.51  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 14.29/14.51      inference('sup-', [status(thm)], ['2', '3'])).
% 14.29/14.51  thf(dt_k2_funct_1, axiom,
% 14.29/14.51    (![A:$i]:
% 14.29/14.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.29/14.51       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 14.29/14.51         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 14.29/14.51  thf('12', plain,
% 14.29/14.51      (![X25 : $i]:
% 14.29/14.51         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 14.29/14.51          | ~ (v1_funct_1 @ X25)
% 14.29/14.51          | ~ (v1_relat_1 @ X25))),
% 14.29/14.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 14.29/14.51  thf('13', plain,
% 14.29/14.51      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 14.29/14.51         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 14.29/14.51      inference('split', [status(esa)], ['0'])).
% 14.29/14.51  thf('14', plain,
% 14.29/14.51      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 14.29/14.51         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 14.29/14.51      inference('sup-', [status(thm)], ['12', '13'])).
% 14.29/14.51  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('16', plain,
% 14.29/14.51      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 14.29/14.51      inference('demod', [status(thm)], ['14', '15'])).
% 14.29/14.51  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['11', '16'])).
% 14.29/14.51  thf('18', plain,
% 14.29/14.51      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('split', [status(esa)], ['0'])).
% 14.29/14.51  thf('19', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.29/14.51  thf(d1_funct_2, axiom,
% 14.29/14.51    (![A:$i,B:$i,C:$i]:
% 14.29/14.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.29/14.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.29/14.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 14.29/14.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 14.29/14.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.29/14.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 14.29/14.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 14.29/14.51  thf(zf_stmt_1, axiom,
% 14.29/14.51    (![B:$i,A:$i]:
% 14.29/14.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.29/14.51       ( zip_tseitin_0 @ B @ A ) ))).
% 14.29/14.51  thf('20', plain,
% 14.29/14.51      (![X42 : $i, X43 : $i]:
% 14.29/14.51         ((zip_tseitin_0 @ X42 @ X43) | ((X42) = (k1_xboole_0)))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.29/14.51  thf('21', plain,
% 14.29/14.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 14.29/14.51  thf(zf_stmt_3, axiom,
% 14.29/14.51    (![C:$i,B:$i,A:$i]:
% 14.29/14.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 14.29/14.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 14.29/14.51  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 14.29/14.51  thf(zf_stmt_5, axiom,
% 14.29/14.51    (![A:$i,B:$i,C:$i]:
% 14.29/14.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.29/14.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 14.29/14.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.29/14.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 14.29/14.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 14.29/14.51  thf('22', plain,
% 14.29/14.51      (![X47 : $i, X48 : $i, X49 : $i]:
% 14.29/14.51         (~ (zip_tseitin_0 @ X47 @ X48)
% 14.29/14.51          | (zip_tseitin_1 @ X49 @ X47 @ X48)
% 14.29/14.51          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47))))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.29/14.51  thf('23', plain,
% 14.29/14.51      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 14.29/14.51        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 14.29/14.51      inference('sup-', [status(thm)], ['21', '22'])).
% 14.29/14.51  thf('24', plain,
% 14.29/14.51      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 14.29/14.51      inference('sup-', [status(thm)], ['20', '23'])).
% 14.29/14.51  thf('25', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('26', plain,
% 14.29/14.51      (![X44 : $i, X45 : $i, X46 : $i]:
% 14.29/14.51         (~ (v1_funct_2 @ X46 @ X44 @ X45)
% 14.29/14.51          | ((X44) = (k1_relset_1 @ X44 @ X45 @ X46))
% 14.29/14.51          | ~ (zip_tseitin_1 @ X46 @ X45 @ X44))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.29/14.51  thf('27', plain,
% 14.29/14.51      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 14.29/14.51        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['25', '26'])).
% 14.29/14.51  thf('28', plain,
% 14.29/14.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf(redefinition_k1_relset_1, axiom,
% 14.29/14.51    (![A:$i,B:$i,C:$i]:
% 14.29/14.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.29/14.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 14.29/14.51  thf('29', plain,
% 14.29/14.51      (![X36 : $i, X37 : $i, X38 : $i]:
% 14.29/14.51         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 14.29/14.51          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 14.29/14.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.29/14.51  thf('30', plain,
% 14.29/14.51      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 14.29/14.51      inference('sup-', [status(thm)], ['28', '29'])).
% 14.29/14.51  thf('31', plain,
% 14.29/14.51      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 14.29/14.51        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 14.29/14.51      inference('demod', [status(thm)], ['27', '30'])).
% 14.29/14.51  thf('32', plain,
% 14.29/14.51      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['24', '31'])).
% 14.29/14.51  thf('33', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.29/14.51  thf(t55_funct_1, axiom,
% 14.29/14.51    (![A:$i]:
% 14.29/14.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.29/14.51       ( ( v2_funct_1 @ A ) =>
% 14.29/14.51         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 14.29/14.51           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 14.29/14.51  thf('34', plain,
% 14.29/14.51      (![X30 : $i]:
% 14.29/14.51         (~ (v2_funct_1 @ X30)
% 14.29/14.51          | ((k2_relat_1 @ X30) = (k1_relat_1 @ (k2_funct_1 @ X30)))
% 14.29/14.51          | ~ (v1_funct_1 @ X30)
% 14.29/14.51          | ~ (v1_relat_1 @ X30))),
% 14.29/14.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 14.29/14.51  thf('35', plain,
% 14.29/14.51      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 14.29/14.51        | ~ (v1_relat_1 @ sk_C)
% 14.29/14.51        | ~ (v1_funct_1 @ sk_C)
% 14.29/14.51        | ~ (v2_funct_1 @ sk_C))),
% 14.29/14.51      inference('sup+', [status(thm)], ['33', '34'])).
% 14.29/14.51  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 14.29/14.51      inference('sup-', [status(thm)], ['2', '3'])).
% 14.29/14.51  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('38', plain, ((v2_funct_1 @ sk_C)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('39', plain,
% 14.29/14.51      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.29/14.51      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 14.29/14.51  thf('40', plain,
% 14.29/14.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf(redefinition_k2_relset_1, axiom,
% 14.29/14.51    (![A:$i,B:$i,C:$i]:
% 14.29/14.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.29/14.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 14.29/14.51  thf('41', plain,
% 14.29/14.51      (![X39 : $i, X40 : $i, X41 : $i]:
% 14.29/14.51         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 14.29/14.51          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 14.29/14.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 14.29/14.51  thf('42', plain,
% 14.29/14.51      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 14.29/14.51      inference('sup-', [status(thm)], ['40', '41'])).
% 14.29/14.51  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_B_1))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('44', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 14.29/14.51      inference('sup+', [status(thm)], ['42', '43'])).
% 14.29/14.51  thf('45', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.29/14.51      inference('demod', [status(thm)], ['39', '44'])).
% 14.29/14.51  thf(t3_funct_2, axiom,
% 14.29/14.51    (![A:$i]:
% 14.29/14.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.29/14.51       ( ( v1_funct_1 @ A ) & 
% 14.29/14.51         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 14.29/14.51         ( m1_subset_1 @
% 14.29/14.51           A @ 
% 14.29/14.51           ( k1_zfmisc_1 @
% 14.29/14.51             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 14.29/14.51  thf('46', plain,
% 14.29/14.51      (![X50 : $i]:
% 14.29/14.51         ((v1_funct_2 @ X50 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))
% 14.29/14.51          | ~ (v1_funct_1 @ X50)
% 14.29/14.51          | ~ (v1_relat_1 @ X50))),
% 14.29/14.51      inference('cnf', [status(esa)], [t3_funct_2])).
% 14.29/14.51  thf('47', plain,
% 14.29/14.51      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ 
% 14.29/14.51         (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 14.29/14.51        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 14.29/14.51        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 14.29/14.51      inference('sup+', [status(thm)], ['45', '46'])).
% 14.29/14.51  thf('48', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.29/14.51  thf('49', plain,
% 14.29/14.51      (![X30 : $i]:
% 14.29/14.51         (~ (v2_funct_1 @ X30)
% 14.29/14.51          | ((k1_relat_1 @ X30) = (k2_relat_1 @ (k2_funct_1 @ X30)))
% 14.29/14.51          | ~ (v1_funct_1 @ X30)
% 14.29/14.51          | ~ (v1_relat_1 @ X30))),
% 14.29/14.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 14.29/14.51  thf('50', plain,
% 14.29/14.51      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 14.29/14.51        | ~ (v1_relat_1 @ sk_C)
% 14.29/14.51        | ~ (v1_funct_1 @ sk_C)
% 14.29/14.51        | ~ (v2_funct_1 @ sk_C))),
% 14.29/14.51      inference('sup+', [status(thm)], ['48', '49'])).
% 14.29/14.51  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 14.29/14.51      inference('sup-', [status(thm)], ['2', '3'])).
% 14.29/14.51  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('54', plain,
% 14.29/14.51      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.29/14.51      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 14.29/14.51  thf('55', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.29/14.51  thf('56', plain,
% 14.29/14.51      (![X25 : $i]:
% 14.29/14.51         ((v1_relat_1 @ (k2_funct_1 @ X25))
% 14.29/14.51          | ~ (v1_funct_1 @ X25)
% 14.29/14.51          | ~ (v1_relat_1 @ X25))),
% 14.29/14.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 14.29/14.51  thf('57', plain,
% 14.29/14.51      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 14.29/14.51        | ~ (v1_relat_1 @ sk_C)
% 14.29/14.51        | ~ (v1_funct_1 @ sk_C))),
% 14.29/14.51      inference('sup+', [status(thm)], ['55', '56'])).
% 14.29/14.51  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 14.29/14.51      inference('sup-', [status(thm)], ['2', '3'])).
% 14.29/14.51  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('60', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['57', '58', '59'])).
% 14.29/14.51  thf('61', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.29/14.51  thf('62', plain,
% 14.29/14.51      (![X25 : $i]:
% 14.29/14.51         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 14.29/14.51          | ~ (v1_funct_1 @ X25)
% 14.29/14.51          | ~ (v1_relat_1 @ X25))),
% 14.29/14.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 14.29/14.51  thf('63', plain,
% 14.29/14.51      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 14.29/14.51        | ~ (v1_relat_1 @ sk_C)
% 14.29/14.51        | ~ (v1_funct_1 @ sk_C))),
% 14.29/14.51      inference('sup+', [status(thm)], ['61', '62'])).
% 14.29/14.51  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 14.29/14.51      inference('sup-', [status(thm)], ['2', '3'])).
% 14.29/14.51  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('66', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['63', '64', '65'])).
% 14.29/14.51  thf('67', plain,
% 14.29/14.51      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ (k1_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['47', '54', '60', '66'])).
% 14.29/14.51  thf('68', plain,
% 14.29/14.51      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A)
% 14.29/14.51        | ((sk_B_1) = (k1_xboole_0)))),
% 14.29/14.51      inference('sup+', [status(thm)], ['32', '67'])).
% 14.29/14.51  thf('69', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.29/14.51  thf('70', plain,
% 14.29/14.51      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('split', [status(esa)], ['0'])).
% 14.29/14.51  thf('71', plain,
% 14.29/14.51      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['69', '70'])).
% 14.29/14.51  thf('72', plain,
% 14.29/14.51      ((((sk_B_1) = (k1_xboole_0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['68', '71'])).
% 14.29/14.51  thf('73', plain,
% 14.29/14.51      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('demod', [status(thm)], ['18', '19', '72'])).
% 14.29/14.51  thf('74', plain,
% 14.29/14.51      ((((sk_B_1) = (k1_xboole_0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['68', '71'])).
% 14.29/14.51  thf(d1_xboole_0, axiom,
% 14.29/14.51    (![A:$i]:
% 14.29/14.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 14.29/14.51  thf('75', plain,
% 14.29/14.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 14.29/14.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 14.29/14.51  thf('76', plain,
% 14.29/14.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf(l3_subset_1, axiom,
% 14.29/14.51    (![A:$i,B:$i]:
% 14.29/14.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 14.29/14.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 14.29/14.51  thf('77', plain,
% 14.29/14.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 14.29/14.51         (~ (r2_hidden @ X11 @ X12)
% 14.29/14.51          | (r2_hidden @ X11 @ X13)
% 14.29/14.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 14.29/14.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 14.29/14.51  thf('78', plain,
% 14.29/14.51      (![X0 : $i]:
% 14.29/14.51         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 14.29/14.51          | ~ (r2_hidden @ X0 @ sk_C))),
% 14.29/14.51      inference('sup-', [status(thm)], ['76', '77'])).
% 14.29/14.51  thf('79', plain,
% 14.29/14.51      (((v1_xboole_0 @ sk_C)
% 14.29/14.51        | (r2_hidden @ (sk_B @ sk_C) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['75', '78'])).
% 14.29/14.51  thf('80', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 14.29/14.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 14.29/14.51  thf('81', plain,
% 14.29/14.51      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['79', '80'])).
% 14.29/14.51  thf('82', plain,
% 14.29/14.51      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 14.29/14.51         | (v1_xboole_0 @ sk_C)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['74', '81'])).
% 14.29/14.51  thf(t113_zfmisc_1, axiom,
% 14.29/14.51    (![A:$i,B:$i]:
% 14.29/14.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 14.29/14.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 14.29/14.51  thf('83', plain,
% 14.29/14.51      (![X9 : $i, X10 : $i]:
% 14.29/14.51         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 14.29/14.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 14.29/14.51  thf('84', plain,
% 14.29/14.51      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 14.29/14.51      inference('simplify', [status(thm)], ['83'])).
% 14.29/14.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 14.29/14.51  thf('85', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 14.29/14.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.29/14.51  thf('86', plain,
% 14.29/14.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 14.29/14.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 14.29/14.51  thf(t7_ordinal1, axiom,
% 14.29/14.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.29/14.51  thf('87', plain,
% 14.29/14.51      (![X31 : $i, X32 : $i]:
% 14.29/14.51         (~ (r2_hidden @ X31 @ X32) | ~ (r1_tarski @ X32 @ X31))),
% 14.29/14.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 14.29/14.51  thf('88', plain,
% 14.29/14.51      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['86', '87'])).
% 14.29/14.51  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['85', '88'])).
% 14.29/14.51  thf('90', plain,
% 14.29/14.51      (((v1_xboole_0 @ sk_C))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('demod', [status(thm)], ['82', '84', '89'])).
% 14.29/14.51  thf(l13_xboole_0, axiom,
% 14.29/14.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 14.29/14.51  thf('91', plain,
% 14.29/14.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 14.29/14.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.29/14.51  thf('92', plain,
% 14.29/14.51      ((((sk_C) = (k1_xboole_0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['90', '91'])).
% 14.29/14.51  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['85', '88'])).
% 14.29/14.51  thf(fc14_relat_1, axiom,
% 14.29/14.51    (![A:$i]:
% 14.29/14.51     ( ( v1_xboole_0 @ A ) =>
% 14.29/14.51       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 14.29/14.51         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 14.29/14.51  thf('94', plain,
% 14.29/14.51      (![X19 : $i]:
% 14.29/14.51         ((v1_xboole_0 @ (k4_relat_1 @ X19)) | ~ (v1_xboole_0 @ X19))),
% 14.29/14.51      inference('cnf', [status(esa)], [fc14_relat_1])).
% 14.29/14.51  thf('95', plain,
% 14.29/14.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 14.29/14.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.29/14.51  thf('96', plain,
% 14.29/14.51      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['94', '95'])).
% 14.29/14.51  thf('97', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.29/14.51      inference('sup-', [status(thm)], ['93', '96'])).
% 14.29/14.51  thf('98', plain,
% 14.29/14.51      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('demod', [status(thm)], ['73', '92', '97'])).
% 14.29/14.51  thf('99', plain,
% 14.29/14.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 14.29/14.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.29/14.51  thf('100', plain,
% 14.29/14.51      (![X42 : $i, X43 : $i]:
% 14.29/14.51         ((zip_tseitin_0 @ X42 @ X43) | ((X42) = (k1_xboole_0)))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.29/14.51  thf('101', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 14.29/14.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.29/14.51  thf('102', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.29/14.51         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 14.29/14.51      inference('sup+', [status(thm)], ['100', '101'])).
% 14.29/14.51  thf('103', plain,
% 14.29/14.51      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['86', '87'])).
% 14.29/14.51  thf('104', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 14.29/14.51      inference('sup-', [status(thm)], ['102', '103'])).
% 14.29/14.51  thf('105', plain,
% 14.29/14.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 14.29/14.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.29/14.51  thf('106', plain,
% 14.29/14.51      ((((sk_B_1) = (k1_xboole_0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['68', '71'])).
% 14.29/14.51  thf('107', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('108', plain,
% 14.29/14.51      (((v1_funct_2 @ sk_C @ sk_A @ k1_xboole_0))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup+', [status(thm)], ['106', '107'])).
% 14.29/14.51  thf('109', plain,
% 14.29/14.51      ((((sk_C) = (k1_xboole_0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['90', '91'])).
% 14.29/14.51  thf('110', plain,
% 14.29/14.51      (((v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('demod', [status(thm)], ['108', '109'])).
% 14.29/14.51  thf('111', plain,
% 14.29/14.51      ((![X0 : $i]:
% 14.29/14.51          ((v1_funct_2 @ k1_xboole_0 @ sk_A @ X0) | ~ (v1_xboole_0 @ X0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup+', [status(thm)], ['105', '110'])).
% 14.29/14.51  thf('112', plain,
% 14.29/14.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 14.29/14.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.29/14.51  thf('113', plain,
% 14.29/14.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 14.29/14.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.29/14.51  thf('114', plain,
% 14.29/14.51      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('demod', [status(thm)], ['73', '92', '97'])).
% 14.29/14.51  thf('115', plain,
% 14.29/14.51      ((![X0 : $i]:
% 14.29/14.51          (~ (v1_funct_2 @ X0 @ k1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ X0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['113', '114'])).
% 14.29/14.51  thf('116', plain,
% 14.29/14.51      ((![X0 : $i, X1 : $i]:
% 14.29/14.51          (~ (v1_funct_2 @ X1 @ X0 @ sk_A)
% 14.29/14.51           | ~ (v1_xboole_0 @ X0)
% 14.29/14.51           | ~ (v1_xboole_0 @ X1)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['112', '115'])).
% 14.29/14.51  thf('117', plain,
% 14.29/14.51      (((~ (v1_xboole_0 @ sk_A)
% 14.29/14.51         | ~ (v1_xboole_0 @ k1_xboole_0)
% 14.29/14.51         | ~ (v1_xboole_0 @ sk_A)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['111', '116'])).
% 14.29/14.51  thf('118', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['85', '88'])).
% 14.29/14.51  thf('119', plain,
% 14.29/14.51      (((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_A)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('demod', [status(thm)], ['117', '118'])).
% 14.29/14.51  thf('120', plain,
% 14.29/14.51      ((~ (v1_xboole_0 @ sk_A))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('simplify', [status(thm)], ['119'])).
% 14.29/14.51  thf('121', plain,
% 14.29/14.51      ((![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['104', '120'])).
% 14.29/14.51  thf(t4_subset_1, axiom,
% 14.29/14.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 14.29/14.51  thf('122', plain,
% 14.29/14.51      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 14.29/14.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.29/14.51  thf('123', plain,
% 14.29/14.51      (![X47 : $i, X48 : $i, X49 : $i]:
% 14.29/14.51         (~ (zip_tseitin_0 @ X47 @ X48)
% 14.29/14.51          | (zip_tseitin_1 @ X49 @ X47 @ X48)
% 14.29/14.51          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47))))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.29/14.51  thf('124', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i]:
% 14.29/14.51         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 14.29/14.51      inference('sup-', [status(thm)], ['122', '123'])).
% 14.29/14.51  thf('125', plain,
% 14.29/14.51      ((![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ sk_A @ X0))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['121', '124'])).
% 14.29/14.51  thf('126', plain,
% 14.29/14.51      ((![X0 : $i, X1 : $i]:
% 14.29/14.51          ((zip_tseitin_1 @ X0 @ sk_A @ X1) | ~ (v1_xboole_0 @ X0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup+', [status(thm)], ['99', '125'])).
% 14.29/14.51  thf('127', plain,
% 14.29/14.51      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 14.29/14.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.29/14.51  thf('128', plain,
% 14.29/14.51      (![X36 : $i, X37 : $i, X38 : $i]:
% 14.29/14.51         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 14.29/14.51          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 14.29/14.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.29/14.51  thf('129', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i]:
% 14.29/14.51         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 14.29/14.51      inference('sup-', [status(thm)], ['127', '128'])).
% 14.29/14.51  thf('130', plain,
% 14.29/14.51      (![X44 : $i, X45 : $i, X46 : $i]:
% 14.29/14.51         (((X44) != (k1_relset_1 @ X44 @ X45 @ X46))
% 14.29/14.51          | (v1_funct_2 @ X46 @ X44 @ X45)
% 14.29/14.51          | ~ (zip_tseitin_1 @ X46 @ X45 @ X44))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.29/14.51  thf('131', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i]:
% 14.29/14.51         (((X1) != (k1_relat_1 @ k1_xboole_0))
% 14.29/14.51          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 14.29/14.51          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 14.29/14.51      inference('sup-', [status(thm)], ['129', '130'])).
% 14.29/14.51  thf('132', plain,
% 14.29/14.51      (![X0 : $i]:
% 14.29/14.51         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 14.29/14.51          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 14.29/14.51      inference('simplify', [status(thm)], ['131'])).
% 14.29/14.51  thf('133', plain,
% 14.29/14.51      (((~ (v1_xboole_0 @ k1_xboole_0)
% 14.29/14.51         | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_A)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['126', '132'])).
% 14.29/14.51  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['85', '88'])).
% 14.29/14.51  thf('135', plain,
% 14.29/14.51      ((((sk_C) = (k1_xboole_0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['90', '91'])).
% 14.29/14.51  thf('136', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_B_1))),
% 14.29/14.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.29/14.51  thf('137', plain,
% 14.29/14.51      ((((k2_relset_1 @ sk_A @ sk_B_1 @ k1_xboole_0) = (sk_B_1)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup+', [status(thm)], ['135', '136'])).
% 14.29/14.51  thf('138', plain,
% 14.29/14.51      ((((sk_B_1) = (k1_xboole_0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['68', '71'])).
% 14.29/14.51  thf('139', plain,
% 14.29/14.51      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 14.29/14.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.29/14.51  thf('140', plain,
% 14.29/14.51      (![X39 : $i, X40 : $i, X41 : $i]:
% 14.29/14.51         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 14.29/14.51          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 14.29/14.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 14.29/14.51  thf('141', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i]:
% 14.29/14.51         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 14.29/14.51      inference('sup-', [status(thm)], ['139', '140'])).
% 14.29/14.51  thf(cc1_funct_1, axiom,
% 14.29/14.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 14.29/14.51  thf('142', plain,
% 14.29/14.51      (![X22 : $i]: ((v1_funct_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 14.29/14.51      inference('cnf', [status(esa)], [cc1_funct_1])).
% 14.29/14.51  thf('143', plain,
% 14.29/14.51      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 14.29/14.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.29/14.51  thf('144', plain,
% 14.29/14.51      (![X33 : $i, X34 : $i, X35 : $i]:
% 14.29/14.51         ((v1_relat_1 @ X33)
% 14.29/14.51          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 14.29/14.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 14.29/14.51  thf('145', plain, ((v1_relat_1 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['143', '144'])).
% 14.29/14.51  thf('146', plain,
% 14.29/14.51      (![X24 : $i]:
% 14.29/14.51         (~ (v2_funct_1 @ X24)
% 14.29/14.51          | ((k2_funct_1 @ X24) = (k4_relat_1 @ X24))
% 14.29/14.51          | ~ (v1_funct_1 @ X24)
% 14.29/14.51          | ~ (v1_relat_1 @ X24))),
% 14.29/14.51      inference('cnf', [status(esa)], [d9_funct_1])).
% 14.29/14.51  thf('147', plain,
% 14.29/14.51      ((~ (v1_funct_1 @ k1_xboole_0)
% 14.29/14.51        | ((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 14.29/14.51        | ~ (v2_funct_1 @ k1_xboole_0))),
% 14.29/14.51      inference('sup-', [status(thm)], ['145', '146'])).
% 14.29/14.51  thf('148', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['85', '88'])).
% 14.29/14.51  thf(cc1_relat_1, axiom,
% 14.29/14.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 14.29/14.51  thf('149', plain,
% 14.29/14.51      (![X18 : $i]: ((v1_relat_1 @ X18) | ~ (v1_xboole_0 @ X18))),
% 14.29/14.51      inference('cnf', [status(esa)], [cc1_relat_1])).
% 14.29/14.51  thf(cc2_funct_1, axiom,
% 14.29/14.51    (![A:$i]:
% 14.29/14.51     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.29/14.51       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 14.29/14.51  thf('150', plain,
% 14.29/14.51      (![X23 : $i]:
% 14.29/14.51         ((v2_funct_1 @ X23)
% 14.29/14.51          | ~ (v1_funct_1 @ X23)
% 14.29/14.51          | ~ (v1_relat_1 @ X23)
% 14.29/14.51          | ~ (v1_xboole_0 @ X23))),
% 14.29/14.51      inference('cnf', [status(esa)], [cc2_funct_1])).
% 14.29/14.51  thf('151', plain,
% 14.29/14.51      (![X0 : $i]:
% 14.29/14.51         (~ (v1_xboole_0 @ X0)
% 14.29/14.51          | ~ (v1_xboole_0 @ X0)
% 14.29/14.51          | ~ (v1_funct_1 @ X0)
% 14.29/14.51          | (v2_funct_1 @ X0))),
% 14.29/14.51      inference('sup-', [status(thm)], ['149', '150'])).
% 14.29/14.51  thf('152', plain,
% 14.29/14.51      (![X0 : $i]:
% 14.29/14.51         ((v2_funct_1 @ X0) | ~ (v1_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 14.29/14.51      inference('simplify', [status(thm)], ['151'])).
% 14.29/14.51  thf('153', plain,
% 14.29/14.51      (![X22 : $i]: ((v1_funct_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 14.29/14.51      inference('cnf', [status(esa)], [cc1_funct_1])).
% 14.29/14.51  thf('154', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_funct_1 @ X0))),
% 14.29/14.51      inference('clc', [status(thm)], ['152', '153'])).
% 14.29/14.51  thf('155', plain, ((v2_funct_1 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['148', '154'])).
% 14.29/14.51  thf('156', plain,
% 14.29/14.51      ((~ (v1_funct_1 @ k1_xboole_0)
% 14.29/14.51        | ((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0)))),
% 14.29/14.51      inference('demod', [status(thm)], ['147', '155'])).
% 14.29/14.51  thf('157', plain,
% 14.29/14.51      ((~ (v1_xboole_0 @ k1_xboole_0)
% 14.29/14.51        | ((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['142', '156'])).
% 14.29/14.51  thf('158', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['85', '88'])).
% 14.29/14.51  thf('159', plain,
% 14.29/14.51      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 14.29/14.51      inference('demod', [status(thm)], ['157', '158'])).
% 14.29/14.51  thf('160', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.29/14.51      inference('sup-', [status(thm)], ['93', '96'])).
% 14.29/14.51  thf('161', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.29/14.51      inference('demod', [status(thm)], ['159', '160'])).
% 14.29/14.51  thf('162', plain,
% 14.29/14.51      (![X30 : $i]:
% 14.29/14.51         (~ (v2_funct_1 @ X30)
% 14.29/14.51          | ((k1_relat_1 @ X30) = (k2_relat_1 @ (k2_funct_1 @ X30)))
% 14.29/14.51          | ~ (v1_funct_1 @ X30)
% 14.29/14.51          | ~ (v1_relat_1 @ X30))),
% 14.29/14.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 14.29/14.51  thf('163', plain,
% 14.29/14.51      ((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 14.29/14.51        | ~ (v1_relat_1 @ k1_xboole_0)
% 14.29/14.51        | ~ (v1_funct_1 @ k1_xboole_0)
% 14.29/14.51        | ~ (v2_funct_1 @ k1_xboole_0))),
% 14.29/14.51      inference('sup+', [status(thm)], ['161', '162'])).
% 14.29/14.51  thf('164', plain, ((v1_relat_1 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['143', '144'])).
% 14.29/14.51  thf('165', plain,
% 14.29/14.51      (![X22 : $i]: ((v1_funct_1 @ X22) | ~ (v1_xboole_0 @ X22))),
% 14.29/14.51      inference('cnf', [status(esa)], [cc1_funct_1])).
% 14.29/14.51  thf('166', plain,
% 14.29/14.51      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 14.29/14.51      inference('demod', [status(thm)], ['157', '158'])).
% 14.29/14.51  thf('167', plain,
% 14.29/14.51      (![X25 : $i]:
% 14.29/14.51         ((v1_funct_1 @ (k2_funct_1 @ X25))
% 14.29/14.51          | ~ (v1_funct_1 @ X25)
% 14.29/14.51          | ~ (v1_relat_1 @ X25))),
% 14.29/14.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 14.29/14.51  thf('168', plain,
% 14.29/14.51      (((v1_funct_1 @ (k4_relat_1 @ k1_xboole_0))
% 14.29/14.51        | ~ (v1_relat_1 @ k1_xboole_0)
% 14.29/14.51        | ~ (v1_funct_1 @ k1_xboole_0))),
% 14.29/14.51      inference('sup+', [status(thm)], ['166', '167'])).
% 14.29/14.51  thf('169', plain, ((v1_relat_1 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['143', '144'])).
% 14.29/14.51  thf('170', plain,
% 14.29/14.51      (((v1_funct_1 @ (k4_relat_1 @ k1_xboole_0))
% 14.29/14.51        | ~ (v1_funct_1 @ k1_xboole_0))),
% 14.29/14.51      inference('demod', [status(thm)], ['168', '169'])).
% 14.29/14.51  thf('171', plain,
% 14.29/14.51      ((~ (v1_xboole_0 @ k1_xboole_0)
% 14.29/14.51        | (v1_funct_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['165', '170'])).
% 14.29/14.51  thf('172', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['85', '88'])).
% 14.29/14.51  thf('173', plain, ((v1_funct_1 @ (k4_relat_1 @ k1_xboole_0))),
% 14.29/14.51      inference('demod', [status(thm)], ['171', '172'])).
% 14.29/14.51  thf('174', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.29/14.51      inference('sup-', [status(thm)], ['93', '96'])).
% 14.29/14.51  thf('175', plain, ((v1_funct_1 @ k1_xboole_0)),
% 14.29/14.51      inference('demod', [status(thm)], ['173', '174'])).
% 14.29/14.51  thf('176', plain, ((v2_funct_1 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['148', '154'])).
% 14.29/14.51  thf('177', plain,
% 14.29/14.51      (((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 14.29/14.51      inference('demod', [status(thm)], ['163', '164', '175', '176'])).
% 14.29/14.51  thf('178', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i]:
% 14.29/14.51         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 14.29/14.51      inference('demod', [status(thm)], ['141', '177'])).
% 14.29/14.51  thf('179', plain,
% 14.29/14.51      ((((sk_B_1) = (k1_xboole_0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['68', '71'])).
% 14.29/14.51  thf('180', plain,
% 14.29/14.51      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('demod', [status(thm)], ['137', '138', '178', '179'])).
% 14.29/14.51  thf('181', plain,
% 14.29/14.51      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 14.29/14.51         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('demod', [status(thm)], ['133', '134', '180'])).
% 14.29/14.51  thf('182', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))),
% 14.29/14.51      inference('demod', [status(thm)], ['98', '181'])).
% 14.29/14.51  thf('183', plain,
% 14.29/14.51      (~
% 14.29/14.51       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 14.29/14.51       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)) | 
% 14.29/14.51       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 14.29/14.51      inference('split', [status(esa)], ['0'])).
% 14.29/14.51  thf('184', plain,
% 14.29/14.51      (~
% 14.29/14.51       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 14.29/14.51      inference('sat_resolution*', [status(thm)], ['17', '182', '183'])).
% 14.29/14.51  thf('185', plain,
% 14.29/14.51      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 14.29/14.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('simpl_trail', [status(thm)], ['10', '184'])).
% 14.29/14.51  thf('186', plain,
% 14.29/14.51      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.29/14.51      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 14.29/14.51  thf('187', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 14.29/14.51      inference('sup-', [status(thm)], ['102', '103'])).
% 14.29/14.51  thf('188', plain,
% 14.29/14.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 14.29/14.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.29/14.51  thf('189', plain,
% 14.29/14.51      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 14.29/14.51      inference('simplify', [status(thm)], ['83'])).
% 14.29/14.51  thf('190', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i]:
% 14.29/14.51         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.29/14.51      inference('sup+', [status(thm)], ['188', '189'])).
% 14.29/14.51  thf('191', plain,
% 14.29/14.51      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 14.29/14.51      inference('sup-', [status(thm)], ['79', '80'])).
% 14.29/14.51  thf('192', plain,
% 14.29/14.51      ((~ (v1_xboole_0 @ k1_xboole_0)
% 14.29/14.51        | ~ (v1_xboole_0 @ sk_B_1)
% 14.29/14.51        | (v1_xboole_0 @ sk_C))),
% 14.29/14.51      inference('sup-', [status(thm)], ['190', '191'])).
% 14.29/14.51  thf('193', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.29/14.51      inference('sup-', [status(thm)], ['85', '88'])).
% 14.29/14.51  thf('194', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['192', '193'])).
% 14.29/14.51  thf('195', plain,
% 14.29/14.51      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C))),
% 14.29/14.51      inference('sup-', [status(thm)], ['187', '194'])).
% 14.29/14.51  thf('196', plain,
% 14.29/14.51      (![X19 : $i]:
% 14.29/14.51         ((v1_xboole_0 @ (k4_relat_1 @ X19)) | ~ (v1_xboole_0 @ X19))),
% 14.29/14.51      inference('cnf', [status(esa)], [fc14_relat_1])).
% 14.29/14.51  thf('197', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.29/14.51  thf('198', plain,
% 14.29/14.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 14.29/14.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.29/14.51  thf('199', plain,
% 14.29/14.51      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 14.29/14.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.29/14.51  thf('200', plain,
% 14.29/14.51      (![X0 : $i, X1 : $i]:
% 14.29/14.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 14.29/14.51      inference('sup+', [status(thm)], ['198', '199'])).
% 14.29/14.51  thf('201', plain,
% 14.29/14.51      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 14.29/14.51         <= (~
% 14.29/14.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 14.29/14.51      inference('split', [status(esa)], ['0'])).
% 14.29/14.51  thf('202', plain,
% 14.29/14.51      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C)))
% 14.29/14.51         <= (~
% 14.29/14.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 14.29/14.51      inference('sup-', [status(thm)], ['200', '201'])).
% 14.29/14.51  thf('203', plain,
% 14.29/14.51      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C)))
% 14.29/14.51         <= (~
% 14.29/14.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 14.29/14.51      inference('sup-', [status(thm)], ['197', '202'])).
% 14.29/14.51  thf('204', plain,
% 14.29/14.51      ((~ (v1_xboole_0 @ sk_C))
% 14.29/14.51         <= (~
% 14.29/14.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 14.29/14.51      inference('sup-', [status(thm)], ['196', '203'])).
% 14.29/14.51  thf('205', plain,
% 14.29/14.51      ((![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0))
% 14.29/14.51         <= (~
% 14.29/14.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 14.29/14.51      inference('sup-', [status(thm)], ['195', '204'])).
% 14.29/14.51  thf('206', plain,
% 14.29/14.51      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 14.29/14.51        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 14.29/14.51      inference('sup-', [status(thm)], ['21', '22'])).
% 14.29/14.51  thf('207', plain,
% 14.29/14.51      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))
% 14.29/14.51         <= (~
% 14.29/14.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 14.29/14.51      inference('sup-', [status(thm)], ['205', '206'])).
% 14.29/14.51  thf('208', plain,
% 14.29/14.51      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 14.29/14.51        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 14.29/14.51      inference('demod', [status(thm)], ['27', '30'])).
% 14.29/14.51  thf('209', plain,
% 14.29/14.51      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 14.29/14.51         <= (~
% 14.29/14.51             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 14.29/14.51      inference('sup-', [status(thm)], ['207', '208'])).
% 14.29/14.51  thf('210', plain,
% 14.29/14.51      (~
% 14.29/14.51       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.29/14.51         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 14.29/14.51      inference('sat_resolution*', [status(thm)], ['17', '182', '183'])).
% 14.29/14.51  thf('211', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 14.29/14.51      inference('simpl_trail', [status(thm)], ['209', '210'])).
% 14.29/14.51  thf('212', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.29/14.51      inference('demod', [status(thm)], ['186', '211'])).
% 14.29/14.51  thf('213', plain,
% 14.29/14.51      (![X50 : $i]:
% 14.29/14.51         ((m1_subset_1 @ X50 @ 
% 14.29/14.51           (k1_zfmisc_1 @ 
% 14.29/14.51            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 14.29/14.51          | ~ (v1_funct_1 @ X50)
% 14.29/14.51          | ~ (v1_relat_1 @ X50))),
% 14.29/14.51      inference('cnf', [status(esa)], [t3_funct_2])).
% 14.29/14.51  thf('214', plain,
% 14.29/14.51      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 14.29/14.51         (k1_zfmisc_1 @ 
% 14.29/14.51          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 14.29/14.51        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 14.29/14.51        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 14.29/14.51      inference('sup+', [status(thm)], ['212', '213'])).
% 14.29/14.51  thf('215', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.29/14.51      inference('demod', [status(thm)], ['39', '44'])).
% 14.29/14.51  thf('216', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['57', '58', '59'])).
% 14.29/14.51  thf('217', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 14.29/14.51      inference('demod', [status(thm)], ['63', '64', '65'])).
% 14.29/14.51  thf('218', plain,
% 14.29/14.51      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 14.29/14.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 14.29/14.51      inference('demod', [status(thm)], ['214', '215', '216', '217'])).
% 14.29/14.51  thf('219', plain, ($false), inference('demod', [status(thm)], ['185', '218'])).
% 14.29/14.51  
% 14.29/14.51  % SZS output end Refutation
% 14.29/14.51  
% 14.29/14.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
