%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6utjH7E1R

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:05 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  178 (1703 expanded)
%              Number of leaves         :   45 ( 494 expanded)
%              Depth                    :   24
%              Number of atoms          : 1175 (25745 expanded)
%              Number of equality atoms :   84 (1238 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('12',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['14','17'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X28 )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','25','26'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

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

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

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

thf('31',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('58',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_partfun1 @ X29 @ X30 )
      | ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf('63',plain,(
    ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_partfun1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('68',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X34 ) ) )
      | ( v1_partfun1 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('69',plain,
    ( ( ( v1_partfun1 @ sk_D @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('70',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('71',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( v1_partfun1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['64','75'])).

thf('77',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('78',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','78'])).

thf('80',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['53','79'])).

thf('81',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['48','80'])).

thf('82',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['41','81'])).

thf('83',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','83'])).

thf('85',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('91',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X17 ) ) )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('97',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('99',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['48','80'])).

thf('101',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','102'])).

thf('104',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 != k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( v1_funct_2 @ X42 @ X41 @ X40 )
      | ( X42 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('105',plain,(
    ! [X41: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('107',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X41: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','102'])).

thf('111',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('113',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','73'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('116',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','119'])).

thf('121',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('125',plain,(
    ! [X35: $i] :
      ( zip_tseitin_0 @ X35 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('127',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['123','129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['103','111','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6utjH7E1R
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.69  % Solved by: fo/fo7.sh
% 0.52/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.69  % done 387 iterations in 0.240s
% 0.52/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.69  % SZS output start Refutation
% 0.52/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.52/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.52/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.69  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.52/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.69  thf(t8_funct_2, conjecture,
% 0.52/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.69       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.52/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.52/0.69           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.52/0.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.52/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.69            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.69          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.52/0.69            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.52/0.69              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.52/0.69                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.52/0.69    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.52/0.69  thf('0', plain,
% 0.52/0.69      ((~ (v1_funct_1 @ sk_D)
% 0.52/0.69        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.52/0.69        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('1', plain,
% 0.52/0.69      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.52/0.69         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.52/0.69      inference('split', [status(esa)], ['0'])).
% 0.52/0.69  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.52/0.69      inference('split', [status(esa)], ['0'])).
% 0.52/0.69  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.52/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.69  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('6', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf(redefinition_k2_relset_1, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.52/0.69  thf('7', plain,
% 0.52/0.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.52/0.69         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.52/0.69          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.52/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.69  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.52/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.69  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.52/0.69      inference('demod', [status(thm)], ['5', '8'])).
% 0.52/0.69  thf('10', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf(cc2_relset_1, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.69  thf('11', plain,
% 0.52/0.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.69         ((v4_relat_1 @ X14 @ X15)
% 0.52/0.69          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.52/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.69  thf('12', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.52/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.69  thf(d18_relat_1, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ( v1_relat_1 @ B ) =>
% 0.52/0.69       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.69  thf('13', plain,
% 0.52/0.69      (![X8 : $i, X9 : $i]:
% 0.52/0.69         (~ (v4_relat_1 @ X8 @ X9)
% 0.52/0.69          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.52/0.69          | ~ (v1_relat_1 @ X8))),
% 0.52/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.69  thf('14', plain,
% 0.52/0.69      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.69  thf('15', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf(cc1_relset_1, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.69       ( v1_relat_1 @ C ) ))).
% 0.52/0.69  thf('16', plain,
% 0.52/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.69         ((v1_relat_1 @ X11)
% 0.52/0.69          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.52/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.69  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.69  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.52/0.69      inference('demod', [status(thm)], ['14', '17'])).
% 0.52/0.69  thf(t11_relset_1, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( v1_relat_1 @ C ) =>
% 0.52/0.69       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.52/0.69           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.52/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.52/0.69  thf('19', plain,
% 0.52/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.52/0.69         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 0.52/0.69          | ~ (r1_tarski @ (k2_relat_1 @ X26) @ X28)
% 0.52/0.69          | (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.52/0.69          | ~ (v1_relat_1 @ X26))),
% 0.52/0.69      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.52/0.69  thf('20', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         (~ (v1_relat_1 @ sk_D)
% 0.52/0.69          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.52/0.69          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.69  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.69  thf('22', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.52/0.69          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.52/0.69      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.69  thf('23', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['9', '22'])).
% 0.52/0.69  thf('24', plain,
% 0.52/0.69      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.52/0.69         <= (~
% 0.52/0.69             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.52/0.69      inference('split', [status(esa)], ['0'])).
% 0.52/0.69  thf('25', plain,
% 0.52/0.69      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.52/0.69      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.69  thf('26', plain,
% 0.52/0.69      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.52/0.69       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.52/0.69       ~ ((v1_funct_1 @ sk_D))),
% 0.52/0.69      inference('split', [status(esa)], ['0'])).
% 0.52/0.69  thf('27', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.52/0.69      inference('sat_resolution*', [status(thm)], ['4', '25', '26'])).
% 0.52/0.69  thf('28', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.52/0.69      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.52/0.69  thf(d1_funct_2, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.69       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.69           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.52/0.69             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.52/0.69         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.69           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.52/0.69             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.52/0.69  thf(zf_stmt_1, axiom,
% 0.52/0.69    (![B:$i,A:$i]:
% 0.52/0.69     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.69       ( zip_tseitin_0 @ B @ A ) ))).
% 0.52/0.69  thf('29', plain,
% 0.52/0.69      (![X35 : $i, X36 : $i]:
% 0.52/0.69         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.69  thf('30', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['9', '22'])).
% 0.52/0.69  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.52/0.69  thf(zf_stmt_3, axiom,
% 0.52/0.69    (![C:$i,B:$i,A:$i]:
% 0.52/0.69     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.52/0.69       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.69  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.52/0.69  thf(zf_stmt_5, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.69       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.52/0.69         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.69           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.69             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.52/0.69  thf('31', plain,
% 0.52/0.69      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.52/0.69         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.52/0.69          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.52/0.69          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.69  thf('32', plain,
% 0.52/0.69      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.52/0.69  thf('33', plain,
% 0.52/0.69      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['29', '32'])).
% 0.52/0.69  thf('34', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['9', '22'])).
% 0.52/0.69  thf(redefinition_k1_relset_1, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.52/0.69  thf('35', plain,
% 0.52/0.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.69         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.52/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.52/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.69  thf('36', plain,
% 0.52/0.69      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.52/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.52/0.69  thf('37', plain,
% 0.52/0.69      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.52/0.69         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.52/0.69          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.52/0.69          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.69  thf('38', plain,
% 0.52/0.69      ((((sk_A) != (k1_relat_1 @ sk_D))
% 0.52/0.69        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.52/0.69        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.52/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.52/0.69  thf('39', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.52/0.69      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.52/0.69  thf('40', plain,
% 0.52/0.69      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.52/0.69        | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 0.52/0.69      inference('clc', [status(thm)], ['38', '39'])).
% 0.52/0.69  thf('41', plain,
% 0.52/0.69      ((((sk_C) = (k1_xboole_0)) | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['33', '40'])).
% 0.52/0.69  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('43', plain,
% 0.52/0.69      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.52/0.69         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.52/0.69          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.52/0.69          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.69  thf('44', plain,
% 0.52/0.69      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.52/0.69        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.69  thf('45', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('46', plain,
% 0.52/0.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.69         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.52/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.52/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.69  thf('47', plain,
% 0.52/0.69      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.52/0.69      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.69  thf('48', plain,
% 0.52/0.69      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.52/0.69      inference('demod', [status(thm)], ['44', '47'])).
% 0.52/0.69  thf('49', plain,
% 0.52/0.69      (![X35 : $i, X36 : $i]:
% 0.52/0.69         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.69  thf('50', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('51', plain,
% 0.52/0.69      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.52/0.69         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.52/0.69          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.52/0.69          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.69  thf('52', plain,
% 0.52/0.69      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['50', '51'])).
% 0.52/0.69  thf('53', plain,
% 0.52/0.69      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['49', '52'])).
% 0.52/0.69  thf('54', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('55', plain,
% 0.52/0.69      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.52/0.69      inference('split', [status(esa)], ['54'])).
% 0.52/0.69  thf('56', plain,
% 0.52/0.69      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('split', [status(esa)], ['54'])).
% 0.52/0.69  thf('57', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['9', '22'])).
% 0.52/0.69  thf(cc1_funct_2, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.69       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.52/0.69         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.52/0.69  thf('58', plain,
% 0.52/0.69      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.69         (~ (v1_funct_1 @ X29)
% 0.52/0.69          | ~ (v1_partfun1 @ X29 @ X30)
% 0.52/0.69          | (v1_funct_2 @ X29 @ X30 @ X31)
% 0.52/0.69          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.52/0.69      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.52/0.69  thf('59', plain,
% 0.52/0.69      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.52/0.69        | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.52/0.69        | ~ (v1_funct_1 @ sk_D))),
% 0.52/0.69      inference('sup-', [status(thm)], ['57', '58'])).
% 0.52/0.69  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('61', plain,
% 0.52/0.69      (((v1_funct_2 @ sk_D @ sk_A @ sk_C) | ~ (v1_partfun1 @ sk_D @ sk_A))),
% 0.52/0.69      inference('demod', [status(thm)], ['59', '60'])).
% 0.52/0.70  thf('62', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.52/0.70      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.52/0.70  thf('63', plain, (~ (v1_partfun1 @ sk_D @ sk_A)),
% 0.52/0.70      inference('clc', [status(thm)], ['61', '62'])).
% 0.52/0.70  thf('64', plain,
% 0.52/0.70      ((~ (v1_partfun1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['56', '63'])).
% 0.52/0.70  thf('65', plain,
% 0.52/0.70      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('split', [status(esa)], ['54'])).
% 0.52/0.70  thf('66', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['9', '22'])).
% 0.52/0.70  thf('67', plain,
% 0.52/0.70      (((m1_subset_1 @ sk_D @ 
% 0.52/0.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.52/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup+', [status(thm)], ['65', '66'])).
% 0.52/0.70  thf(cc1_partfun1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( v1_xboole_0 @ A ) =>
% 0.52/0.70       ( ![C:$i]:
% 0.52/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.70           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.52/0.70  thf('68', plain,
% 0.52/0.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ X32)
% 0.52/0.70          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X34)))
% 0.52/0.70          | (v1_partfun1 @ X33 @ X32))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.52/0.70  thf('69', plain,
% 0.52/0.70      ((((v1_partfun1 @ sk_D @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.52/0.70         <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['67', '68'])).
% 0.52/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.52/0.70  thf('70', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.52/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.70  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.52/0.70  thf('71', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.52/0.70      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.52/0.70  thf(t69_xboole_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.70       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.52/0.70  thf('72', plain,
% 0.52/0.70      (![X3 : $i, X4 : $i]:
% 0.52/0.70         (~ (r1_xboole_0 @ X3 @ X4)
% 0.52/0.70          | ~ (r1_tarski @ X3 @ X4)
% 0.52/0.70          | (v1_xboole_0 @ X3))),
% 0.52/0.70      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.52/0.70  thf('73', plain,
% 0.52/0.70      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['71', '72'])).
% 0.52/0.70  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['70', '73'])).
% 0.52/0.70  thf('75', plain,
% 0.52/0.70      (((v1_partfun1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.52/0.70      inference('demod', [status(thm)], ['69', '74'])).
% 0.52/0.70  thf('76', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.52/0.70      inference('demod', [status(thm)], ['64', '75'])).
% 0.52/0.70  thf('77', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.52/0.70      inference('split', [status(esa)], ['54'])).
% 0.52/0.70  thf('78', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.52/0.70      inference('sat_resolution*', [status(thm)], ['76', '77'])).
% 0.52/0.70  thf('79', plain, (((sk_B) != (k1_xboole_0))),
% 0.52/0.70      inference('simpl_trail', [status(thm)], ['55', '78'])).
% 0.52/0.70  thf('80', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.52/0.70      inference('simplify_reflect-', [status(thm)], ['53', '79'])).
% 0.52/0.70  thf('81', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.52/0.70      inference('demod', [status(thm)], ['48', '80'])).
% 0.52/0.70  thf('82', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.52/0.70      inference('demod', [status(thm)], ['41', '81'])).
% 0.52/0.70  thf('83', plain, (((sk_C) = (k1_xboole_0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['82'])).
% 0.52/0.70  thf('84', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 0.52/0.70      inference('demod', [status(thm)], ['28', '83'])).
% 0.52/0.70  thf('85', plain,
% 0.52/0.70      (![X35 : $i, X36 : $i]:
% 0.52/0.70         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.70  thf('86', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.52/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.70  thf('87', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.52/0.70      inference('sup+', [status(thm)], ['85', '86'])).
% 0.52/0.70  thf('88', plain,
% 0.52/0.70      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['71', '72'])).
% 0.52/0.70  thf('89', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['87', '88'])).
% 0.52/0.70  thf('90', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['9', '22'])).
% 0.52/0.70  thf(cc4_relset_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( v1_xboole_0 @ A ) =>
% 0.52/0.70       ( ![C:$i]:
% 0.52/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.52/0.70           ( v1_xboole_0 @ C ) ) ) ))).
% 0.52/0.70  thf('91', plain,
% 0.52/0.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ X17)
% 0.52/0.70          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X17)))
% 0.52/0.70          | (v1_xboole_0 @ X18))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.52/0.70  thf('92', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_C))),
% 0.52/0.70      inference('sup-', [status(thm)], ['90', '91'])).
% 0.52/0.70  thf('93', plain,
% 0.52/0.70      (![X0 : $i]: ((zip_tseitin_0 @ sk_C @ X0) | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['89', '92'])).
% 0.52/0.70  thf(l13_xboole_0, axiom,
% 0.52/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.70  thf('94', plain,
% 0.52/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.70  thf('95', plain,
% 0.52/0.70      (![X0 : $i]: ((zip_tseitin_0 @ sk_C @ X0) | ((sk_D) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['93', '94'])).
% 0.52/0.70  thf('96', plain,
% 0.52/0.70      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.52/0.70  thf('97', plain,
% 0.52/0.70      ((((sk_D) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['95', '96'])).
% 0.52/0.70  thf('98', plain,
% 0.52/0.70      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.52/0.70        | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 0.52/0.70      inference('clc', [status(thm)], ['38', '39'])).
% 0.52/0.70  thf('99', plain,
% 0.52/0.70      ((((sk_D) = (k1_xboole_0)) | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['97', '98'])).
% 0.52/0.70  thf('100', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.52/0.70      inference('demod', [status(thm)], ['48', '80'])).
% 0.52/0.70  thf('101', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.52/0.70      inference('demod', [status(thm)], ['99', '100'])).
% 0.52/0.70  thf('102', plain, (((sk_D) = (k1_xboole_0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['101'])).
% 0.52/0.70  thf('103', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.52/0.70      inference('demod', [status(thm)], ['84', '102'])).
% 0.52/0.70  thf('104', plain,
% 0.52/0.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.52/0.70         (((X40) != (k1_xboole_0))
% 0.52/0.70          | ((X41) = (k1_xboole_0))
% 0.52/0.70          | (v1_funct_2 @ X42 @ X41 @ X40)
% 0.52/0.70          | ((X42) != (k1_xboole_0))
% 0.52/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.70  thf('105', plain,
% 0.52/0.70      (![X41 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.52/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ k1_xboole_0)))
% 0.52/0.70          | (v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0)
% 0.52/0.70          | ((X41) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['104'])).
% 0.52/0.70  thf('106', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.52/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.52/0.70  thf(t3_subset, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.70  thf('107', plain,
% 0.52/0.70      (![X5 : $i, X7 : $i]:
% 0.52/0.70         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.52/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.70  thf('108', plain,
% 0.52/0.70      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['106', '107'])).
% 0.52/0.70  thf('109', plain,
% 0.52/0.70      (![X41 : $i]:
% 0.52/0.70         ((v1_funct_2 @ k1_xboole_0 @ X41 @ k1_xboole_0)
% 0.52/0.70          | ((X41) = (k1_xboole_0)))),
% 0.52/0.70      inference('demod', [status(thm)], ['105', '108'])).
% 0.52/0.70  thf('110', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.52/0.70      inference('demod', [status(thm)], ['84', '102'])).
% 0.52/0.70  thf('111', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['109', '110'])).
% 0.52/0.70  thf('112', plain,
% 0.52/0.70      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['106', '107'])).
% 0.52/0.70  thf('113', plain,
% 0.52/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.70         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.52/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.70  thf('114', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['112', '113'])).
% 0.52/0.70  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['70', '73'])).
% 0.52/0.70  thf(fc10_relat_1, axiom,
% 0.52/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.52/0.70  thf('116', plain,
% 0.52/0.70      (![X10 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ (k1_relat_1 @ X10)) | ~ (v1_xboole_0 @ X10))),
% 0.52/0.70      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.52/0.70  thf('117', plain,
% 0.52/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.70  thf('118', plain,
% 0.52/0.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['116', '117'])).
% 0.52/0.70  thf('119', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['115', '118'])).
% 0.52/0.70  thf('120', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('demod', [status(thm)], ['114', '119'])).
% 0.52/0.70  thf('121', plain,
% 0.52/0.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.52/0.70         (((X37) != (k1_relset_1 @ X37 @ X38 @ X39))
% 0.52/0.70          | (v1_funct_2 @ X39 @ X37 @ X38)
% 0.52/0.70          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.70  thf('122', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((X1) != (k1_xboole_0))
% 0.52/0.70          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.52/0.70          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['120', '121'])).
% 0.52/0.70  thf('123', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.70          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['122'])).
% 0.52/0.70  thf('124', plain,
% 0.52/0.70      (![X35 : $i, X36 : $i]:
% 0.52/0.70         ((zip_tseitin_0 @ X35 @ X36) | ((X36) != (k1_xboole_0)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.70  thf('125', plain, (![X35 : $i]: (zip_tseitin_0 @ X35 @ k1_xboole_0)),
% 0.52/0.70      inference('simplify', [status(thm)], ['124'])).
% 0.52/0.70  thf('126', plain,
% 0.52/0.70      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['106', '107'])).
% 0.52/0.70  thf('127', plain,
% 0.52/0.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.52/0.70         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.52/0.70          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.52/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.52/0.70  thf('128', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['126', '127'])).
% 0.52/0.70  thf('129', plain,
% 0.52/0.70      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['125', '128'])).
% 0.52/0.70  thf('130', plain,
% 0.52/0.70      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.52/0.70      inference('demod', [status(thm)], ['123', '129'])).
% 0.52/0.70  thf('131', plain, ($false),
% 0.52/0.70      inference('demod', [status(thm)], ['103', '111', '130'])).
% 0.52/0.70  
% 0.52/0.70  % SZS output end Refutation
% 0.52/0.70  
% 0.52/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
