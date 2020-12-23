%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jwGaome0sw

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:29 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :  204 (1302 expanded)
%              Number of leaves         :   52 ( 414 expanded)
%              Depth                    :   25
%              Number of atoms          : 1354 (20153 expanded)
%              Number of equality atoms :   89 ( 790 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_funct_1 @ X23 )
        = ( k4_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X24: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
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

thf('32',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k1_relat_1 @ X25 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('35',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['27','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','39'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X44: $i] :
      ( ( v1_funct_2 @ X44 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('42',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('44',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('47',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('57',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('58',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('60',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('63',plain,(
    ! [X24: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('64',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','55','61','67'])).

thf('69',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('70',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','72'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('74',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18
        = ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X15 ) @ ( sk_C @ X18 @ X15 ) ) @ X15 )
      | ( r2_hidden @ ( sk_C @ X18 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('75',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('77',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('79',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('80',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['74','86'])).

thf('88',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('91',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('95',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('96',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['94','96','97'])).

thf('99',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['89','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('101',plain,(
    ! [X20: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X20 ) )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
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

thf('106',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X45 ) @ X46 )
      | ( v1_funct_2 @ X45 @ ( k1_relat_1 @ X45 ) @ X46 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('108',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('109',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('110',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('111',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['73','99','104','112'])).

thf('114',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','113','114'])).

thf('116',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','115'])).

thf('117',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['27','38'])).

thf('118',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('119',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('120',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('124',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('125',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','125'])).

thf('127',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','128'])).

thf('130',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('131',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('132',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','125'])).

thf('134',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('135',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','113','114'])).

thf('139',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['132','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['121','140'])).

thf('142',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['118','141'])).

thf('143',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['117','142'])).

thf('144',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('145',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('147',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('148',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('149',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['116','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jwGaome0sw
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:24:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.16/1.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.16/1.33  % Solved by: fo/fo7.sh
% 1.16/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.16/1.33  % done 1333 iterations in 0.908s
% 1.16/1.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.16/1.33  % SZS output start Refutation
% 1.16/1.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.16/1.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.16/1.33  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.16/1.33  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.16/1.33  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.16/1.33  thf(sk_B_type, type, sk_B: $i).
% 1.16/1.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.16/1.33  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.16/1.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.16/1.33  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 1.16/1.33  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.16/1.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.16/1.33  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.16/1.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.16/1.33  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.16/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.16/1.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.16/1.33  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.16/1.33  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.16/1.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.16/1.33  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.16/1.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.16/1.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.16/1.33  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.16/1.33  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.16/1.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.16/1.33  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.16/1.33  thf(t31_funct_2, conjecture,
% 1.16/1.33    (![A:$i,B:$i,C:$i]:
% 1.16/1.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.16/1.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.16/1.33       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.16/1.33         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.16/1.33           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.16/1.33           ( m1_subset_1 @
% 1.16/1.33             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.16/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.16/1.33    (~( ![A:$i,B:$i,C:$i]:
% 1.16/1.33        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.16/1.33            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.16/1.33          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.16/1.33            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.16/1.33              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.16/1.33              ( m1_subset_1 @
% 1.16/1.33                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.16/1.33    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.16/1.33  thf('0', plain,
% 1.16/1.33      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 1.16/1.33        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 1.16/1.33        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.33             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.16/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.33  thf('1', plain,
% 1.16/1.33      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.16/1.34         <= (~
% 1.16/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf('2', plain, ((v1_funct_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf(d9_funct_1, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.16/1.34       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.16/1.34  thf('3', plain,
% 1.16/1.34      (![X23 : $i]:
% 1.16/1.34         (~ (v2_funct_1 @ X23)
% 1.16/1.34          | ((k2_funct_1 @ X23) = (k4_relat_1 @ X23))
% 1.16/1.34          | ~ (v1_funct_1 @ X23)
% 1.16/1.34          | ~ (v1_relat_1 @ X23))),
% 1.16/1.34      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.16/1.34  thf('4', plain,
% 1.16/1.34      ((~ (v1_relat_1 @ sk_C_1)
% 1.16/1.34        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 1.16/1.34        | ~ (v2_funct_1 @ sk_C_1))),
% 1.16/1.34      inference('sup-', [status(thm)], ['2', '3'])).
% 1.16/1.34  thf('5', plain,
% 1.16/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf(cc1_relset_1, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.34       ( v1_relat_1 @ C ) ))).
% 1.16/1.34  thf('6', plain,
% 1.16/1.34      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.16/1.34         ((v1_relat_1 @ X27)
% 1.16/1.34          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.16/1.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.16/1.34  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 1.16/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.16/1.34  thf('8', plain, ((v2_funct_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('9', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.16/1.34  thf('10', plain,
% 1.16/1.34      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 1.16/1.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.16/1.34         <= (~
% 1.16/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.16/1.34      inference('demod', [status(thm)], ['1', '9'])).
% 1.16/1.34  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 1.16/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.16/1.34  thf(dt_k2_funct_1, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.16/1.34       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.16/1.34         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.16/1.34  thf('12', plain,
% 1.16/1.34      (![X24 : $i]:
% 1.16/1.34         ((v1_funct_1 @ (k2_funct_1 @ X24))
% 1.16/1.34          | ~ (v1_funct_1 @ X24)
% 1.16/1.34          | ~ (v1_relat_1 @ X24))),
% 1.16/1.34      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.16/1.34  thf('13', plain,
% 1.16/1.34      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 1.16/1.34         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf('14', plain,
% 1.16/1.34      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 1.16/1.34         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.16/1.34      inference('sup-', [status(thm)], ['12', '13'])).
% 1.16/1.34  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('16', plain,
% 1.16/1.34      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 1.16/1.34      inference('demod', [status(thm)], ['14', '15'])).
% 1.16/1.34  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['11', '16'])).
% 1.16/1.34  thf('18', plain,
% 1.16/1.34      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 1.16/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf('19', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.16/1.34  thf(d1_funct_2, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.34       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.16/1.34           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.16/1.34             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.16/1.34         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.16/1.34           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.16/1.34             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.16/1.34  thf(zf_stmt_1, axiom,
% 1.16/1.34    (![B:$i,A:$i]:
% 1.16/1.34     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.16/1.34       ( zip_tseitin_0 @ B @ A ) ))).
% 1.16/1.34  thf('20', plain,
% 1.16/1.34      (![X36 : $i, X37 : $i]:
% 1.16/1.34         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.34  thf('21', plain,
% 1.16/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.16/1.34  thf(zf_stmt_3, axiom,
% 1.16/1.34    (![C:$i,B:$i,A:$i]:
% 1.16/1.34     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.16/1.34       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.16/1.34  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.16/1.34  thf(zf_stmt_5, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.34       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.16/1.34         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.16/1.34           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.16/1.34             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.16/1.34  thf('22', plain,
% 1.16/1.34      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.16/1.34         (~ (zip_tseitin_0 @ X41 @ X42)
% 1.16/1.34          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 1.16/1.34          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.16/1.34  thf('23', plain,
% 1.16/1.34      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.16/1.34        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['21', '22'])).
% 1.16/1.34  thf('24', plain,
% 1.16/1.34      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['20', '23'])).
% 1.16/1.34  thf('25', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('26', plain,
% 1.16/1.34      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.16/1.34         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 1.16/1.34          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 1.16/1.34          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.16/1.34  thf('27', plain,
% 1.16/1.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.16/1.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['25', '26'])).
% 1.16/1.34  thf('28', plain,
% 1.16/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf(redefinition_k1_relset_1, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.16/1.34  thf('29', plain,
% 1.16/1.34      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.16/1.34         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.16/1.34          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.16/1.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.16/1.34  thf('30', plain,
% 1.16/1.34      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('sup-', [status(thm)], ['28', '29'])).
% 1.16/1.34  thf('31', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.16/1.34  thf(t55_funct_1, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.16/1.34       ( ( v2_funct_1 @ A ) =>
% 1.16/1.34         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.16/1.34           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.16/1.34  thf('32', plain,
% 1.16/1.34      (![X25 : $i]:
% 1.16/1.34         (~ (v2_funct_1 @ X25)
% 1.16/1.34          | ((k1_relat_1 @ X25) = (k2_relat_1 @ (k2_funct_1 @ X25)))
% 1.16/1.34          | ~ (v1_funct_1 @ X25)
% 1.16/1.34          | ~ (v1_relat_1 @ X25))),
% 1.16/1.34      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.16/1.34  thf('33', plain,
% 1.16/1.34      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 1.16/1.34        | ~ (v1_relat_1 @ sk_C_1)
% 1.16/1.34        | ~ (v1_funct_1 @ sk_C_1)
% 1.16/1.34        | ~ (v2_funct_1 @ sk_C_1))),
% 1.16/1.34      inference('sup+', [status(thm)], ['31', '32'])).
% 1.16/1.34  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 1.16/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.16/1.34  thf('35', plain, ((v1_funct_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('36', plain, ((v2_funct_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('37', plain,
% 1.16/1.34      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 1.16/1.34  thf('38', plain,
% 1.16/1.34      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1)
% 1.16/1.34         = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('demod', [status(thm)], ['30', '37'])).
% 1.16/1.34  thf('39', plain,
% 1.16/1.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.16/1.34        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1))))),
% 1.16/1.34      inference('demod', [status(thm)], ['27', '38'])).
% 1.16/1.34  thf('40', plain,
% 1.16/1.34      ((((sk_B) = (k1_xboole_0))
% 1.16/1.34        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1))))),
% 1.16/1.34      inference('sup-', [status(thm)], ['24', '39'])).
% 1.16/1.34  thf(t3_funct_2, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.16/1.34       ( ( v1_funct_1 @ A ) & 
% 1.16/1.34         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.16/1.34         ( m1_subset_1 @
% 1.16/1.34           A @ 
% 1.16/1.34           ( k1_zfmisc_1 @
% 1.16/1.34             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.16/1.34  thf('41', plain,
% 1.16/1.34      (![X44 : $i]:
% 1.16/1.34         ((v1_funct_2 @ X44 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))
% 1.16/1.34          | ~ (v1_funct_1 @ X44)
% 1.16/1.34          | ~ (v1_relat_1 @ X44))),
% 1.16/1.34      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.16/1.34  thf('42', plain,
% 1.16/1.34      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ 
% 1.16/1.34         (k1_relat_1 @ (k4_relat_1 @ sk_C_1)) @ sk_A)
% 1.16/1.34        | ((sk_B) = (k1_xboole_0))
% 1.16/1.34        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 1.16/1.34        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('sup+', [status(thm)], ['40', '41'])).
% 1.16/1.34  thf('43', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.16/1.34  thf('44', plain,
% 1.16/1.34      (![X25 : $i]:
% 1.16/1.34         (~ (v2_funct_1 @ X25)
% 1.16/1.34          | ((k2_relat_1 @ X25) = (k1_relat_1 @ (k2_funct_1 @ X25)))
% 1.16/1.34          | ~ (v1_funct_1 @ X25)
% 1.16/1.34          | ~ (v1_relat_1 @ X25))),
% 1.16/1.34      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.16/1.34  thf('45', plain,
% 1.16/1.34      ((((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 1.16/1.34        | ~ (v1_relat_1 @ sk_C_1)
% 1.16/1.34        | ~ (v1_funct_1 @ sk_C_1)
% 1.16/1.34        | ~ (v2_funct_1 @ sk_C_1))),
% 1.16/1.34      inference('sup+', [status(thm)], ['43', '44'])).
% 1.16/1.34  thf('46', plain, ((v1_relat_1 @ sk_C_1)),
% 1.16/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.16/1.34  thf('47', plain, ((v1_funct_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('48', plain, ((v2_funct_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('49', plain,
% 1.16/1.34      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 1.16/1.34  thf('50', plain,
% 1.16/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf(redefinition_k2_relset_1, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.34       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.16/1.34  thf('51', plain,
% 1.16/1.34      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.16/1.34         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 1.16/1.34          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.16/1.34      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.16/1.34  thf('52', plain,
% 1.16/1.34      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('sup-', [status(thm)], ['50', '51'])).
% 1.16/1.34  thf('53', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('54', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 1.16/1.34      inference('sup+', [status(thm)], ['52', '53'])).
% 1.16/1.34  thf('55', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('demod', [status(thm)], ['49', '54'])).
% 1.16/1.34  thf('56', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.16/1.34  thf('57', plain,
% 1.16/1.34      (![X24 : $i]:
% 1.16/1.34         ((v1_relat_1 @ (k2_funct_1 @ X24))
% 1.16/1.34          | ~ (v1_funct_1 @ X24)
% 1.16/1.34          | ~ (v1_relat_1 @ X24))),
% 1.16/1.34      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.16/1.34  thf('58', plain,
% 1.16/1.34      (((v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 1.16/1.34        | ~ (v1_relat_1 @ sk_C_1)
% 1.16/1.34        | ~ (v1_funct_1 @ sk_C_1))),
% 1.16/1.34      inference('sup+', [status(thm)], ['56', '57'])).
% 1.16/1.34  thf('59', plain, ((v1_relat_1 @ sk_C_1)),
% 1.16/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.16/1.34  thf('60', plain, ((v1_funct_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('61', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.16/1.34  thf('62', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.16/1.34  thf('63', plain,
% 1.16/1.34      (![X24 : $i]:
% 1.16/1.34         ((v1_funct_1 @ (k2_funct_1 @ X24))
% 1.16/1.34          | ~ (v1_funct_1 @ X24)
% 1.16/1.34          | ~ (v1_relat_1 @ X24))),
% 1.16/1.34      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.16/1.34  thf('64', plain,
% 1.16/1.34      (((v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 1.16/1.34        | ~ (v1_relat_1 @ sk_C_1)
% 1.16/1.34        | ~ (v1_funct_1 @ sk_C_1))),
% 1.16/1.34      inference('sup+', [status(thm)], ['62', '63'])).
% 1.16/1.34  thf('65', plain, ((v1_relat_1 @ sk_C_1)),
% 1.16/1.34      inference('sup-', [status(thm)], ['5', '6'])).
% 1.16/1.34  thf('66', plain, ((v1_funct_1 @ sk_C_1)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('67', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.16/1.34  thf('68', plain,
% 1.16/1.34      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A)
% 1.16/1.34        | ((sk_B) = (k1_xboole_0)))),
% 1.16/1.34      inference('demod', [status(thm)], ['42', '55', '61', '67'])).
% 1.16/1.34  thf('69', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.16/1.34  thf('70', plain,
% 1.16/1.34      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 1.16/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf('71', plain,
% 1.16/1.34      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A))
% 1.16/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['69', '70'])).
% 1.16/1.34  thf('72', plain,
% 1.16/1.34      ((((sk_B) = (k1_xboole_0)))
% 1.16/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['68', '71'])).
% 1.16/1.34  thf('73', plain,
% 1.16/1.34      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ k1_xboole_0 @ sk_A))
% 1.16/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.16/1.34      inference('demod', [status(thm)], ['18', '19', '72'])).
% 1.16/1.34  thf(d5_relat_1, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.16/1.34       ( ![C:$i]:
% 1.16/1.34         ( ( r2_hidden @ C @ B ) <=>
% 1.16/1.34           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.16/1.34  thf('74', plain,
% 1.16/1.34      (![X15 : $i, X18 : $i]:
% 1.16/1.34         (((X18) = (k2_relat_1 @ X15))
% 1.16/1.34          | (r2_hidden @ 
% 1.16/1.34             (k4_tarski @ (sk_D @ X18 @ X15) @ (sk_C @ X18 @ X15)) @ X15)
% 1.16/1.34          | (r2_hidden @ (sk_C @ X18 @ X15) @ X18))),
% 1.16/1.34      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.16/1.34  thf(t60_relat_1, axiom,
% 1.16/1.34    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.16/1.34     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.16/1.34  thf('75', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.16/1.34  thf(l13_xboole_0, axiom,
% 1.16/1.34    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.16/1.34  thf('76', plain,
% 1.16/1.34      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.34      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.34  thf('77', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.16/1.34  thf('78', plain,
% 1.16/1.34      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.34      inference('sup+', [status(thm)], ['76', '77'])).
% 1.16/1.34  thf(t4_subset_1, axiom,
% 1.16/1.34    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.16/1.34  thf('79', plain,
% 1.16/1.34      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 1.16/1.34      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.16/1.34  thf(t5_subset, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.16/1.34          ( v1_xboole_0 @ C ) ) ))).
% 1.16/1.34  thf('80', plain,
% 1.16/1.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.16/1.34         (~ (r2_hidden @ X9 @ X10)
% 1.16/1.34          | ~ (v1_xboole_0 @ X11)
% 1.16/1.34          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t5_subset])).
% 1.16/1.34  thf('81', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['79', '80'])).
% 1.16/1.34  thf('82', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.34         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 1.16/1.34          | ~ (v1_xboole_0 @ X0)
% 1.16/1.34          | ~ (v1_xboole_0 @ X2))),
% 1.16/1.34      inference('sup-', [status(thm)], ['78', '81'])).
% 1.16/1.34  thf('83', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.34      inference('condensation', [status(thm)], ['82'])).
% 1.16/1.34  thf('84', plain,
% 1.16/1.34      (![X0 : $i]:
% 1.16/1.34         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['75', '83'])).
% 1.16/1.34  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.16/1.34  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.34  thf('86', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.16/1.34      inference('demod', [status(thm)], ['84', '85'])).
% 1.16/1.34  thf('87', plain,
% 1.16/1.34      (![X0 : $i]:
% 1.16/1.34         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 1.16/1.34          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['74', '86'])).
% 1.16/1.34  thf('88', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.16/1.34  thf('89', plain,
% 1.16/1.34      (![X0 : $i]:
% 1.16/1.34         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 1.16/1.34      inference('demod', [status(thm)], ['87', '88'])).
% 1.16/1.34  thf('90', plain,
% 1.16/1.34      ((((sk_B) = (k1_xboole_0)))
% 1.16/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['68', '71'])).
% 1.16/1.34  thf('91', plain,
% 1.16/1.34      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('92', plain,
% 1.16/1.34      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.16/1.34         (~ (r2_hidden @ X9 @ X10)
% 1.16/1.34          | ~ (v1_xboole_0 @ X11)
% 1.16/1.34          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t5_subset])).
% 1.16/1.34  thf('93', plain,
% 1.16/1.34      (![X0 : $i]:
% 1.16/1.34         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.16/1.34          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.16/1.34      inference('sup-', [status(thm)], ['91', '92'])).
% 1.16/1.34  thf('94', plain,
% 1.16/1.34      ((![X0 : $i]:
% 1.16/1.34          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 1.16/1.34           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 1.16/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['90', '93'])).
% 1.16/1.34  thf(t113_zfmisc_1, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.16/1.34       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.16/1.34  thf('95', plain,
% 1.16/1.34      (![X3 : $i, X4 : $i]:
% 1.16/1.34         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.16/1.34  thf('96', plain,
% 1.16/1.34      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('simplify', [status(thm)], ['95'])).
% 1.16/1.34  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.34  thf('98', plain,
% 1.16/1.34      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1))
% 1.16/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.16/1.34      inference('demod', [status(thm)], ['94', '96', '97'])).
% 1.16/1.34  thf('99', plain,
% 1.16/1.34      ((((sk_C_1) = (k1_xboole_0)))
% 1.16/1.34         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['89', '98'])).
% 1.16/1.34  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.34  thf(fc14_relat_1, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( v1_xboole_0 @ A ) =>
% 1.16/1.34       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 1.16/1.34         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 1.16/1.34  thf('101', plain,
% 1.16/1.34      (![X20 : $i]:
% 1.16/1.34         ((v1_xboole_0 @ (k4_relat_1 @ X20)) | ~ (v1_xboole_0 @ X20))),
% 1.16/1.34      inference('cnf', [status(esa)], [fc14_relat_1])).
% 1.16/1.34  thf('102', plain,
% 1.16/1.34      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.34      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.34  thf('103', plain,
% 1.16/1.34      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['101', '102'])).
% 1.16/1.34  thf('104', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['100', '103'])).
% 1.16/1.34  thf('105', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.16/1.34  thf(t4_funct_2, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.16/1.34       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.16/1.34         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.16/1.34           ( m1_subset_1 @
% 1.16/1.34             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.16/1.34  thf('106', plain,
% 1.16/1.34      (![X45 : $i, X46 : $i]:
% 1.16/1.34         (~ (r1_tarski @ (k2_relat_1 @ X45) @ X46)
% 1.16/1.34          | (v1_funct_2 @ X45 @ (k1_relat_1 @ X45) @ X46)
% 1.16/1.34          | ~ (v1_funct_1 @ X45)
% 1.16/1.34          | ~ (v1_relat_1 @ X45))),
% 1.16/1.34      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.16/1.34  thf('107', plain,
% 1.16/1.34      (![X0 : $i]:
% 1.16/1.34         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 1.16/1.34          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.16/1.34          | ~ (v1_funct_1 @ k1_xboole_0)
% 1.16/1.34          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['105', '106'])).
% 1.16/1.34  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.16/1.34  thf('108', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 1.16/1.34      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.16/1.34  thf(t45_ordinal1, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 1.16/1.34       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 1.16/1.34  thf('109', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [t45_ordinal1])).
% 1.16/1.34  thf('110', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [t45_ordinal1])).
% 1.16/1.34  thf('111', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.34      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.16/1.34  thf('112', plain,
% 1.16/1.34      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.16/1.34      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 1.16/1.34  thf('113', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 1.16/1.34      inference('demod', [status(thm)], ['73', '99', '104', '112'])).
% 1.16/1.34  thf('114', plain,
% 1.16/1.34      (~
% 1.16/1.34       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.34         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.16/1.34       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 1.16/1.34       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf('115', plain,
% 1.16/1.34      (~
% 1.16/1.34       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.34         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.16/1.34      inference('sat_resolution*', [status(thm)], ['17', '113', '114'])).
% 1.16/1.34  thf('116', plain,
% 1.16/1.34      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 1.16/1.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.16/1.34      inference('simpl_trail', [status(thm)], ['10', '115'])).
% 1.16/1.34  thf('117', plain,
% 1.16/1.34      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.16/1.34        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1))))),
% 1.16/1.34      inference('demod', [status(thm)], ['27', '38'])).
% 1.16/1.34  thf('118', plain,
% 1.16/1.34      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 1.16/1.34        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.16/1.34      inference('sup-', [status(thm)], ['21', '22'])).
% 1.16/1.34  thf('119', plain,
% 1.16/1.34      (![X36 : $i, X37 : $i]:
% 1.16/1.34         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.34  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.34  thf('121', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.16/1.34      inference('sup+', [status(thm)], ['119', '120'])).
% 1.16/1.34  thf('122', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('demod', [status(thm)], ['49', '54'])).
% 1.16/1.34  thf('123', plain,
% 1.16/1.34      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.34      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.34  thf('124', plain,
% 1.16/1.34      (![X3 : $i, X4 : $i]:
% 1.16/1.34         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.16/1.34  thf('125', plain,
% 1.16/1.34      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 1.16/1.34      inference('simplify', [status(thm)], ['124'])).
% 1.16/1.34  thf('126', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.34      inference('sup+', [status(thm)], ['123', '125'])).
% 1.16/1.34  thf('127', plain,
% 1.16/1.34      (![X44 : $i]:
% 1.16/1.34         ((m1_subset_1 @ X44 @ 
% 1.16/1.34           (k1_zfmisc_1 @ 
% 1.16/1.34            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))))
% 1.16/1.34          | ~ (v1_funct_1 @ X44)
% 1.16/1.34          | ~ (v1_relat_1 @ X44))),
% 1.16/1.34      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.16/1.34  thf('128', plain,
% 1.16/1.34      (![X0 : $i]:
% 1.16/1.34         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.16/1.34          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.16/1.34          | ~ (v1_relat_1 @ X0)
% 1.16/1.34          | ~ (v1_funct_1 @ X0))),
% 1.16/1.34      inference('sup+', [status(thm)], ['126', '127'])).
% 1.16/1.34  thf('129', plain,
% 1.16/1.34      ((~ (v1_xboole_0 @ sk_B)
% 1.16/1.34        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 1.16/1.34        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 1.16/1.34        | (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['122', '128'])).
% 1.16/1.34  thf('130', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.16/1.34  thf('131', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.16/1.34  thf('132', plain,
% 1.16/1.34      ((~ (v1_xboole_0 @ sk_B)
% 1.16/1.34        | (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 1.16/1.34      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.16/1.34  thf('133', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.34      inference('sup+', [status(thm)], ['123', '125'])).
% 1.16/1.34  thf('134', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['4', '7', '8'])).
% 1.16/1.34  thf('135', plain,
% 1.16/1.34      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.16/1.34         <= (~
% 1.16/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.16/1.34      inference('split', [status(esa)], ['0'])).
% 1.16/1.34  thf('136', plain,
% 1.16/1.34      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 1.16/1.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.16/1.34         <= (~
% 1.16/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.16/1.34      inference('sup-', [status(thm)], ['134', '135'])).
% 1.16/1.34  thf('137', plain,
% 1.16/1.34      (((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.16/1.34         | ~ (v1_xboole_0 @ sk_B)))
% 1.16/1.34         <= (~
% 1.16/1.34             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.34               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.16/1.34      inference('sup-', [status(thm)], ['133', '136'])).
% 1.16/1.34  thf('138', plain,
% 1.16/1.34      (~
% 1.16/1.34       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.16/1.34         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.16/1.34      inference('sat_resolution*', [status(thm)], ['17', '113', '114'])).
% 1.16/1.34  thf('139', plain,
% 1.16/1.34      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.16/1.34        | ~ (v1_xboole_0 @ sk_B))),
% 1.16/1.34      inference('simpl_trail', [status(thm)], ['137', '138'])).
% 1.16/1.34  thf('140', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.16/1.34      inference('clc', [status(thm)], ['132', '139'])).
% 1.16/1.34  thf('141', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 1.16/1.34      inference('sup-', [status(thm)], ['121', '140'])).
% 1.16/1.34  thf('142', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 1.16/1.34      inference('demod', [status(thm)], ['118', '141'])).
% 1.16/1.34  thf('143', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('demod', [status(thm)], ['117', '142'])).
% 1.16/1.34  thf('144', plain,
% 1.16/1.34      (![X44 : $i]:
% 1.16/1.34         ((m1_subset_1 @ X44 @ 
% 1.16/1.34           (k1_zfmisc_1 @ 
% 1.16/1.34            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))))
% 1.16/1.34          | ~ (v1_funct_1 @ X44)
% 1.16/1.34          | ~ (v1_relat_1 @ X44))),
% 1.16/1.34      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.16/1.34  thf('145', plain,
% 1.16/1.34      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 1.16/1.34         (k1_zfmisc_1 @ 
% 1.16/1.34          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C_1)) @ sk_A)))
% 1.16/1.34        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 1.16/1.34        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('sup+', [status(thm)], ['143', '144'])).
% 1.16/1.34  thf('146', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 1.16/1.34      inference('demod', [status(thm)], ['49', '54'])).
% 1.16/1.34  thf('147', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.16/1.34  thf('148', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 1.16/1.34      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.16/1.34  thf('149', plain,
% 1.16/1.34      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 1.16/1.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.16/1.34      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 1.16/1.34  thf('150', plain, ($false), inference('demod', [status(thm)], ['116', '149'])).
% 1.16/1.34  
% 1.16/1.34  % SZS output end Refutation
% 1.16/1.34  
% 1.16/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
