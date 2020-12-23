%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xPXzSy90hX

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:06 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  167 (1949 expanded)
%              Number of leaves         :   38 ( 563 expanded)
%              Depth                    :   24
%              Number of atoms          : 1108 (28114 expanded)
%              Number of equality atoms :   89 (1525 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X30 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('51',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('52',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['58','61'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('63',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('64',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','64'])).

thf('66',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('70',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('72',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['68','74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('77',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('79',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('80',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('88',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','88'])).

thf('90',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','25','26'])).

thf('91',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['89','90'])).

thf('92',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','91'])).

thf('93',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('94',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','94'])).

thf('96',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['48','95'])).

thf('97',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['43','96'])).

thf('98',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['36','97'])).

thf('99',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('100',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf('103',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','103'])).

thf('105',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('107',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('109',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','103'])).

thf('112',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('113',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('115',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','103'])).

thf('118',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('119',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['110','111','113','116','117','118'])).

thf('120',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('121',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['43','96'])).

thf('122',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['110','111','113','116','117','118'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','64'])).

thf('125',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['68','74'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['105','119','125','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xPXzSy90hX
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 362 iterations in 0.221s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.47/0.68  thf(t8_funct_2, conjecture,
% 0.47/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.47/0.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.68           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.47/0.68             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.68        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.68            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.47/0.68            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.68              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.47/0.68                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.47/0.68  thf('0', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ sk_D)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.47/0.68        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.47/0.68         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.47/0.68      inference('split', [status(esa)], ['0'])).
% 0.47/0.68  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.47/0.68      inference('split', [status(esa)], ['0'])).
% 0.47/0.68  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.68  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('6', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.68         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.47/0.68          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.68  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.68  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['5', '8'])).
% 0.47/0.68  thf('10', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc2_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.68  thf('11', plain,
% 0.47/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.68         ((v4_relat_1 @ X19 @ X20)
% 0.47/0.68          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.68  thf('12', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.47/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.68  thf(d18_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ B ) =>
% 0.47/0.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.68  thf('13', plain,
% 0.47/0.68      (![X14 : $i, X15 : $i]:
% 0.47/0.68         (~ (v4_relat_1 @ X14 @ X15)
% 0.47/0.68          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.47/0.68          | ~ (v1_relat_1 @ X14))),
% 0.47/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.68  thf('14', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.68  thf('15', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc1_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( v1_relat_1 @ C ) ))).
% 0.47/0.68  thf('16', plain,
% 0.47/0.68      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.68         ((v1_relat_1 @ X16)
% 0.47/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.68  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.68  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.47/0.68      inference('demod', [status(thm)], ['14', '17'])).
% 0.47/0.68  thf(t11_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ C ) =>
% 0.47/0.68       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.47/0.68           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.47/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.68         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 0.47/0.68          | ~ (r1_tarski @ (k2_relat_1 @ X28) @ X30)
% 0.47/0.68          | (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.47/0.68          | ~ (v1_relat_1 @ X28))),
% 0.47/0.68      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ sk_D)
% 0.47/0.68          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.47/0.68          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.68  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.68  thf('22', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.47/0.68          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.47/0.68      inference('demod', [status(thm)], ['20', '21'])).
% 0.47/0.68  thf('23', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['9', '22'])).
% 0.47/0.68  thf('24', plain,
% 0.47/0.68      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.47/0.68         <= (~
% 0.47/0.68             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.47/0.68      inference('split', [status(esa)], ['0'])).
% 0.47/0.68  thf('25', plain,
% 0.47/0.68      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.68  thf('26', plain,
% 0.47/0.68      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.47/0.68       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.47/0.68       ~ ((v1_funct_1 @ sk_D))),
% 0.47/0.68      inference('split', [status(esa)], ['0'])).
% 0.47/0.68  thf('27', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.47/0.68      inference('sat_resolution*', [status(thm)], ['4', '25', '26'])).
% 0.47/0.68  thf('28', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.47/0.68  thf(d1_funct_2, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_1, axiom,
% 0.47/0.68    (![B:$i,A:$i]:
% 0.47/0.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.68       ( zip_tseitin_0 @ B @ A ) ))).
% 0.47/0.68  thf('29', plain,
% 0.47/0.68      (![X31 : $i, X32 : $i]:
% 0.47/0.68         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.68  thf('30', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['9', '22'])).
% 0.47/0.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.47/0.68  thf(zf_stmt_3, axiom,
% 0.47/0.68    (![C:$i,B:$i,A:$i]:
% 0.47/0.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.47/0.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.47/0.68  thf(zf_stmt_5, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.47/0.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.68  thf('31', plain,
% 0.47/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.68         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.47/0.68          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.47/0.68          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.68  thf('32', plain,
% 0.47/0.68      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.68  thf('33', plain,
% 0.47/0.68      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['29', '32'])).
% 0.47/0.68  thf('34', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['9', '22'])).
% 0.47/0.68  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.68  thf('35', plain,
% 0.47/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.68         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.47/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.68  thf('36', plain,
% 0.47/0.68      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.68  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('38', plain,
% 0.47/0.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.47/0.68         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.47/0.68          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.47/0.68          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.68  thf('39', plain,
% 0.47/0.68      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.47/0.68        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.68  thf('40', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('41', plain,
% 0.47/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.68         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.47/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.68  thf('42', plain,
% 0.47/0.68      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.68  thf('43', plain,
% 0.47/0.68      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.47/0.68      inference('demod', [status(thm)], ['39', '42'])).
% 0.47/0.68  thf('44', plain,
% 0.47/0.68      (![X31 : $i, X32 : $i]:
% 0.47/0.68         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.68  thf('45', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('46', plain,
% 0.47/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.68         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.47/0.68          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.47/0.68          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.68  thf('47', plain,
% 0.47/0.68      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.47/0.68  thf('48', plain,
% 0.47/0.68      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['44', '47'])).
% 0.47/0.68  thf('49', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('50', plain,
% 0.47/0.68      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.47/0.68      inference('split', [status(esa)], ['49'])).
% 0.47/0.68  thf(t4_subset_1, axiom,
% 0.47/0.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.68  thf('51', plain,
% 0.47/0.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.68  thf('52', plain,
% 0.47/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.47/0.68         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.47/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.68  thf('53', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.68  thf('54', plain,
% 0.47/0.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.68  thf('55', plain,
% 0.47/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.68         ((v4_relat_1 @ X19 @ X20)
% 0.47/0.68          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.68  thf('56', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.47/0.68      inference('sup-', [status(thm)], ['54', '55'])).
% 0.47/0.68  thf('57', plain,
% 0.47/0.68      (![X14 : $i, X15 : $i]:
% 0.47/0.68         (~ (v4_relat_1 @ X14 @ X15)
% 0.47/0.68          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.47/0.68          | ~ (v1_relat_1 @ X14))),
% 0.47/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.68  thf('58', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.68          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.47/0.68  thf('59', plain,
% 0.47/0.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.68  thf('60', plain,
% 0.47/0.68      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.68         ((v1_relat_1 @ X16)
% 0.47/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.68  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.47/0.68  thf('62', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.47/0.68      inference('demod', [status(thm)], ['58', '61'])).
% 0.47/0.68  thf(t3_xboole_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.68  thf('63', plain,
% 0.47/0.68      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.47/0.68  thf('64', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.68  thf('65', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['53', '64'])).
% 0.47/0.68  thf('66', plain,
% 0.47/0.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.47/0.68         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 0.47/0.68          | (v1_funct_2 @ X35 @ X33 @ X34)
% 0.47/0.68          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.68  thf('67', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         (((X1) != (k1_xboole_0))
% 0.47/0.68          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.47/0.68          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.68  thf('68', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.68          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['67'])).
% 0.47/0.68  thf('69', plain,
% 0.47/0.68      (![X31 : $i, X32 : $i]:
% 0.47/0.68         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.68  thf('70', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 0.47/0.68      inference('simplify', [status(thm)], ['69'])).
% 0.47/0.68  thf('71', plain,
% 0.47/0.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.68  thf('72', plain,
% 0.47/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.68         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.47/0.68          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.47/0.68          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.68  thf('73', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['71', '72'])).
% 0.47/0.68  thf('74', plain,
% 0.47/0.68      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.47/0.68      inference('sup-', [status(thm)], ['70', '73'])).
% 0.47/0.68  thf('75', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.47/0.68      inference('demod', [status(thm)], ['68', '74'])).
% 0.47/0.68  thf('76', plain,
% 0.47/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('split', [status(esa)], ['49'])).
% 0.47/0.68  thf('77', plain,
% 0.47/0.68      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.47/0.68         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.47/0.68      inference('split', [status(esa)], ['0'])).
% 0.47/0.68  thf('78', plain,
% 0.47/0.68      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.47/0.68         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['76', '77'])).
% 0.47/0.68  thf(t113_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.68  thf('79', plain,
% 0.47/0.68      (![X5 : $i, X6 : $i]:
% 0.47/0.68         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.68  thf('80', plain,
% 0.47/0.68      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['79'])).
% 0.47/0.68  thf('81', plain,
% 0.47/0.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('split', [status(esa)], ['49'])).
% 0.47/0.68  thf('82', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('83', plain,
% 0.47/0.68      (((m1_subset_1 @ sk_D @ 
% 0.47/0.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup+', [status(thm)], ['81', '82'])).
% 0.47/0.68  thf('84', plain,
% 0.47/0.68      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup+', [status(thm)], ['80', '83'])).
% 0.47/0.68  thf(t3_subset, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.68  thf('85', plain,
% 0.47/0.68      (![X8 : $i, X9 : $i]:
% 0.47/0.68         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.68  thf('86', plain,
% 0.47/0.68      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['84', '85'])).
% 0.47/0.68  thf('87', plain,
% 0.47/0.68      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.47/0.68  thf('88', plain,
% 0.47/0.68      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['86', '87'])).
% 0.47/0.68  thf('89', plain,
% 0.47/0.68      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.47/0.68         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('demod', [status(thm)], ['78', '88'])).
% 0.47/0.68  thf('90', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.47/0.68      inference('sat_resolution*', [status(thm)], ['4', '25', '26'])).
% 0.47/0.68  thf('91', plain,
% 0.47/0.68      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.47/0.68         <= ((((sk_A) = (k1_xboole_0))))),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['89', '90'])).
% 0.47/0.68  thf('92', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['75', '91'])).
% 0.47/0.68  thf('93', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.47/0.68      inference('split', [status(esa)], ['49'])).
% 0.47/0.68  thf('94', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.47/0.68      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 0.47/0.68  thf('95', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['50', '94'])).
% 0.47/0.68  thf('96', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['48', '95'])).
% 0.47/0.68  thf('97', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['43', '96'])).
% 0.47/0.68  thf('98', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['36', '97'])).
% 0.47/0.68  thf('99', plain,
% 0.47/0.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.47/0.68         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 0.47/0.68          | (v1_funct_2 @ X35 @ X33 @ X34)
% 0.47/0.68          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.68  thf('100', plain,
% 0.47/0.68      ((((sk_A) != (sk_A))
% 0.47/0.68        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.47/0.68        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.68  thf('101', plain,
% 0.47/0.68      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.47/0.68        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.47/0.68      inference('simplify', [status(thm)], ['100'])).
% 0.47/0.68  thf('102', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.47/0.68      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.47/0.68  thf('103', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.47/0.68      inference('clc', [status(thm)], ['101', '102'])).
% 0.47/0.68  thf('104', plain, (((sk_C) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['33', '103'])).
% 0.47/0.68  thf('105', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 0.47/0.68      inference('demod', [status(thm)], ['28', '104'])).
% 0.47/0.68  thf('106', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['9', '22'])).
% 0.47/0.68  thf('107', plain,
% 0.47/0.68      (![X8 : $i, X9 : $i]:
% 0.47/0.68         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.68  thf('108', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['106', '107'])).
% 0.47/0.68  thf(d10_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.68  thf('109', plain,
% 0.47/0.68      (![X0 : $i, X2 : $i]:
% 0.47/0.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.68  thf('110', plain,
% 0.47/0.68      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 0.47/0.68        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['108', '109'])).
% 0.47/0.68  thf('111', plain, (((sk_C) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['33', '103'])).
% 0.47/0.68  thf('112', plain,
% 0.47/0.68      (![X5 : $i, X6 : $i]:
% 0.47/0.68         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.68  thf('113', plain,
% 0.47/0.68      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['112'])).
% 0.47/0.68  thf('114', plain,
% 0.47/0.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.68  thf('115', plain,
% 0.47/0.68      (![X8 : $i, X9 : $i]:
% 0.47/0.68         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.68  thf('116', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.47/0.68      inference('sup-', [status(thm)], ['114', '115'])).
% 0.47/0.68  thf('117', plain, (((sk_C) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['33', '103'])).
% 0.47/0.68  thf('118', plain,
% 0.47/0.68      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['112'])).
% 0.47/0.68  thf('119', plain, (((k1_xboole_0) = (sk_D))),
% 0.47/0.68      inference('demod', [status(thm)],
% 0.47/0.68                ['110', '111', '113', '116', '117', '118'])).
% 0.47/0.68  thf('120', plain,
% 0.47/0.68      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.47/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.68  thf('121', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.47/0.68      inference('demod', [status(thm)], ['43', '96'])).
% 0.47/0.68  thf('122', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['120', '121'])).
% 0.47/0.68  thf('123', plain, (((k1_xboole_0) = (sk_D))),
% 0.47/0.68      inference('demod', [status(thm)],
% 0.47/0.68                ['110', '111', '113', '116', '117', '118'])).
% 0.47/0.68  thf('124', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['53', '64'])).
% 0.47/0.68  thf('125', plain, (((k1_xboole_0) = (sk_A))),
% 0.47/0.68      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.47/0.68  thf('126', plain,
% 0.47/0.68      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.47/0.68      inference('demod', [status(thm)], ['68', '74'])).
% 0.47/0.68  thf('127', plain, ($false),
% 0.47/0.68      inference('demod', [status(thm)], ['105', '119', '125', '126'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
