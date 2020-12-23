%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tny7m8r14H

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:06 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  154 (1479 expanded)
%              Number of leaves         :   36 ( 424 expanded)
%              Depth                    :   27
%              Number of atoms          : 1076 (22995 expanded)
%              Number of equality atoms :   87 (1224 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
   <= ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('12',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['14','17'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X32 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','25','26'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('52',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','25','26'])).

thf('55',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('58',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D_1 )
      = ( k1_relat_1 @ sk_D_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('60',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,
    ( ( v4_relat_1 @ sk_D_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('65',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('67',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('68',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','71'])).

thf('73',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('74',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0 )
      | ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C )
      | ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('77',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('82',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','82'])).

thf('84',plain,
    ( ( v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','83'])).

thf('85',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['55','84'])).

thf('86',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('87',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['85','86'])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','87'])).

thf('89',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['48','88'])).

thf('90',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['43','89'])).

thf('91',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D_1 )
    = sk_A ),
    inference(demod,[status(thm)],['36','90'])).

thf('92',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('93',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf('96',plain,(
    ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','96'])).

thf('98',plain,(
    ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','97'])).

thf('99',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['43','89'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('100',plain,(
    ! [X41: $i] :
      ( ( v1_funct_2 @ X41 @ ( k1_relat_1 @ X41 ) @ ( k2_relat_1 @ X41 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('101',plain,
    ( ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('103',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('107',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) )
    | ( sk_C
      = ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('109',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('110',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D_1 ) )
    | ( sk_C
      = ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','96'])).

thf('112',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('113',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','96'])).

thf('114',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['104','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['98','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tny7m8r14H
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 343 iterations in 0.211s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.63  thf(t8_funct_2, conjecture,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.46/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.63           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.46/0.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.63            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.46/0.63            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.63              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.46/0.63                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_D_1)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)
% 0.46/0.63        | ~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      ((~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))
% 0.46/0.63         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)))),
% 0.46/0.63      inference('split', [status(esa)], ['0'])).
% 0.46/0.63  thf('2', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('3', plain, ((~ (v1_funct_1 @ sk_D_1)) <= (~ ((v1_funct_1 @ sk_D_1)))),
% 0.46/0.63      inference('split', [status(esa)], ['0'])).
% 0.46/0.63  thf('4', plain, (((v1_funct_1 @ sk_D_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.63  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_1) @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.63         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.46/0.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.63  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['5', '8'])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.63         ((v4_relat_1 @ X21 @ X22)
% 0.46/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.63  thf('12', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf(d18_relat_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ B ) =>
% 0.46/0.63       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X14 : $i, X15 : $i]:
% 0.46/0.63         (~ (v4_relat_1 @ X14 @ X15)
% 0.46/0.63          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.46/0.63          | ~ (v1_relat_1 @ X14))),
% 0.46/0.63      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc1_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( v1_relat_1 @ C ) ))).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.63         ((v1_relat_1 @ X18)
% 0.46/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.63  thf('17', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.63  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['14', '17'])).
% 0.46/0.63  thf(t11_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ C ) =>
% 0.46/0.63       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.46/0.63           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.63         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.46/0.63          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ X32)
% 0.46/0.63          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.46/0.63          | ~ (v1_relat_1 @ X30))),
% 0.46/0.63      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ sk_D_1)
% 0.46/0.63          | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.63          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.63  thf('21', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.63          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['9', '22'])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      ((~ (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.46/0.63         <= (~
% 0.46/0.63             ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.63               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.46/0.63      inference('split', [status(esa)], ['0'])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) | 
% 0.46/0.63       ~ ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.46/0.63       ~ ((v1_funct_1 @ sk_D_1))),
% 0.46/0.63      inference('split', [status(esa)], ['0'])).
% 0.46/0.63  thf('27', plain, (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['4', '25', '26'])).
% 0.46/0.63  thf('28', plain, (~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.46/0.63  thf(d1_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_1, axiom,
% 0.46/0.63    (![B:$i,A:$i]:
% 0.46/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      (![X33 : $i, X34 : $i]:
% 0.46/0.63         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['9', '22'])).
% 0.46/0.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_3, axiom,
% 0.46/0.63    (![C:$i,B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_5, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.64         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.64           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.64             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.64         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.46/0.64          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.46/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A)
% 0.46/0.64        | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['29', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '22'])).
% 0.46/0.64  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.64         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.46/0.64          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (((k1_relset_1 @ sk_A @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('37', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.64         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.46/0.64          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 0.46/0.64          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.46/0.64        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.64         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.46/0.64          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.46/0.64        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['39', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X33 : $i, X34 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.64         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.46/0.64          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.46/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.46/0.64        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['44', '47'])).
% 0.46/0.64  thf('49', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['49'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['49'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      ((~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))
% 0.46/0.64         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      ((~ (v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C))
% 0.46/0.64         <= (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)) & 
% 0.46/0.64             (((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.64  thf('54', plain, (~ ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['4', '25', '26'])).
% 0.46/0.64  thf('55', plain,
% 0.46/0.64      ((~ (v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['49'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      (((k1_relset_1 @ sk_A @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1)))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['56', '57'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['49'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X21 @ X22)
% 0.46/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (((v4_relat_1 @ sk_D_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i]:
% 0.46/0.64         (~ (v4_relat_1 @ X14 @ X15)
% 0.46/0.64          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.46/0.64          | ~ (v1_relat_1 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.64         | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ k1_xboole_0)))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('66', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (((r1_tarski @ (k1_relat_1 @ sk_D_1) @ k1_xboole_0))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.64  thf('68', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.64  thf(d10_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X0 : $i, X2 : $i]:
% 0.46/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['67', '70'])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      ((((k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D_1) = (k1_xboole_0)))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['58', '71'])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.64         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 0.46/0.64          | (v1_funct_2 @ X37 @ X35 @ X36)
% 0.46/0.64          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.64         | ~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0)
% 0.46/0.64         | (v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C)))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      ((((v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C)
% 0.46/0.64         | ~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0)))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['74'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('split', [status(esa)], ['49'])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '22'])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['76', '77'])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.64         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.46/0.64          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.46/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      ((((zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0)
% 0.46/0.64         | ~ (zip_tseitin_0 @ sk_C @ k1_xboole_0)))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      (![X33 : $i, X34 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('82', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 0.46/0.64      inference('simplify', [status(thm)], ['81'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ k1_xboole_0))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '82'])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_D_1 @ k1_xboole_0 @ sk_C))
% 0.46/0.64         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.64      inference('demod', [status(thm)], ['75', '83'])).
% 0.46/0.64  thf('85', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['55', '84'])).
% 0.46/0.64  thf('86', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.46/0.64      inference('split', [status(esa)], ['49'])).
% 0.46/0.64  thf('87', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['85', '86'])).
% 0.46/0.64  thf('88', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['50', '87'])).
% 0.46/0.64  thf('89', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['48', '88'])).
% 0.46/0.64  thf('90', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['43', '89'])).
% 0.46/0.64  thf('91', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D_1) = (sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['36', '90'])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.64         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 0.46/0.64          | (v1_funct_2 @ X37 @ X35 @ X36)
% 0.46/0.64          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('93', plain,
% 0.46/0.64      ((((sk_A) != (sk_A))
% 0.46/0.64        | ~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A)
% 0.46/0.64        | (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['91', '92'])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)
% 0.46/0.64        | ~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('simplify', [status(thm)], ['93'])).
% 0.46/0.64  thf('95', plain, (~ (v1_funct_2 @ sk_D_1 @ sk_A @ sk_C)),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.46/0.64  thf('96', plain, (~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_A)),
% 0.46/0.64      inference('clc', [status(thm)], ['94', '95'])).
% 0.46/0.64  thf('97', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['33', '96'])).
% 0.46/0.64  thf('98', plain, (~ (v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0)),
% 0.46/0.64      inference('demod', [status(thm)], ['28', '97'])).
% 0.46/0.64  thf('99', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['43', '89'])).
% 0.46/0.64  thf(t3_funct_2, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v1_funct_1 @ A ) & 
% 0.46/0.64         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.46/0.64         ( m1_subset_1 @
% 0.46/0.64           A @ 
% 0.46/0.64           ( k1_zfmisc_1 @
% 0.46/0.64             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('100', plain,
% 0.46/0.64      (![X41 : $i]:
% 0.46/0.64         ((v1_funct_2 @ X41 @ (k1_relat_1 @ X41) @ (k2_relat_1 @ X41))
% 0.46/0.64          | ~ (v1_funct_1 @ X41)
% 0.46/0.64          | ~ (v1_relat_1 @ X41))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_D_1 @ sk_A @ (k2_relat_1 @ sk_D_1))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_D_1)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_D_1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['99', '100'])).
% 0.46/0.64  thf('102', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('103', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('104', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.46/0.64  thf('105', plain,
% 0.46/0.64      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_1) @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      (![X0 : $i, X2 : $i]:
% 0.46/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.64  thf('107', plain,
% 0.46/0.64      ((~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))
% 0.46/0.64        | ((sk_C) = (k2_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['105', '106'])).
% 0.46/0.64  thf('108', plain,
% 0.46/0.64      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('109', plain,
% 0.46/0.64      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('110', plain,
% 0.46/0.64      ((~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D_1))
% 0.46/0.64        | ((sk_C) = (k2_relat_1 @ sk_D_1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.46/0.64  thf('111', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['33', '96'])).
% 0.46/0.64  thf('112', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.64  thf('113', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['33', '96'])).
% 0.46/0.64  thf('114', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_D_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 0.46/0.64  thf('115', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0)),
% 0.46/0.64      inference('demod', [status(thm)], ['104', '114'])).
% 0.46/0.64  thf('116', plain, ($false), inference('demod', [status(thm)], ['98', '115'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
