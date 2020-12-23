%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v74dZhh13G

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:07 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  224 (6232 expanded)
%              Number of leaves         :   51 (1854 expanded)
%              Depth                    :   40
%              Number of atoms          : 1489 (61380 expanded)
%              Number of equality atoms :  129 (4710 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
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
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C_2 ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_2 ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( v4_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['14','19'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X42 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['4','27','28'])).

thf('30',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

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

thf('31',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

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

thf('33',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_2 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('53',plain,(
    ! [X27: $i] :
      ( ( ( k9_relat_1 @ X27 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('54',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X29 @ X30 ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('55',plain,(
    ! [X11: $i] :
      ( ( r1_xboole_0 @ X11 @ X11 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('56',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('59',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','65'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('68',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('70',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','70'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k9_relat_1 @ X25 @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('73',plain,(
    ! [X28: $i] :
      ( ( ( k2_relat_1 @ X28 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X28 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['68','69'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','70'])).

thf('78',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['68','69'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','79'])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['68','69'])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X42 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('87',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['68','69'])).

thf('88',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['82'])).

thf('89',plain,(
    ! [X28: $i] :
      ( ( ( k1_relat_1 @ X28 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X28 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('90',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['68','69'])).

thf('92',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','93','94'])).

thf('96',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['82'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45
       != ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X44 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('104',plain,(
    ! [X43: $i] :
      ( zip_tseitin_0 @ X43 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','93','94'])).

thf('106',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['102','108'])).

thf('110',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('111',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_2 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('114',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('115',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('117',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('120',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('121',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('124',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['112','124'])).

thf('126',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['4','27','28'])).

thf('127',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['125','126'])).

thf('128',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['109','127'])).

thf('129',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('130',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['128','129'])).

thf('131',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','130'])).

thf('132',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['50','131'])).

thf('133',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['45','132'])).

thf('134',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_2 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','133'])).

thf('135',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45
       != ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('136',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

thf('139',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','139'])).

thf('141',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','140'])).

thf('142',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('144',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ( sk_C_2
      = ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('146',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('147',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k2_relat_1 @ sk_D ) )
    | ( sk_C_2
      = ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','139'])).

thf('149',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('150',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','139'])).

thf('151',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf('152',plain,(
    ! [X28: $i] :
      ( ( ( k2_relat_1 @ X28 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X28 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('153',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('155',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['45','132'])).

thf('156',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['141','157'])).

thf('159',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('160',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['156'])).

thf('164',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('165',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('166',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_D ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['159','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('169',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['102','108'])).

thf('171',plain,(
    $false ),
    inference(demod,[status(thm)],['158','169','170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v74dZhh13G
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:42:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.98  % Solved by: fo/fo7.sh
% 0.76/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.98  % done 437 iterations in 0.496s
% 0.76/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.98  % SZS output start Refutation
% 0.76/0.98  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.76/0.98  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.76/0.98  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.98  thf(t8_funct_2, conjecture,
% 0.76/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.98       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.76/0.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.76/0.98           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.76/0.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.98        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.98            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.98          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.76/0.98            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.76/0.98              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.76/0.98                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.76/0.98    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.76/0.98  thf('0', plain,
% 0.76/0.98      ((~ (v1_funct_1 @ sk_D)
% 0.76/0.98        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_2)
% 0.76/0.98        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('1', plain,
% 0.76/0.98      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_2))
% 0.76/0.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.98  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C_2)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('6', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(redefinition_k2_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.76/0.98  thf('7', plain,
% 0.76/0.98      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.76/0.98         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.76/0.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.98  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.98  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_2)),
% 0.76/0.98      inference('demod', [status(thm)], ['5', '8'])).
% 0.76/0.98  thf('10', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.98  thf('11', plain,
% 0.76/0.98      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.98         ((v4_relat_1 @ X31 @ X32)
% 0.76/0.98          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.98  thf('12', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.76/0.98      inference('sup-', [status(thm)], ['10', '11'])).
% 0.76/0.98  thf(d18_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) =>
% 0.76/0.98       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.76/0.98  thf('13', plain,
% 0.76/0.98      (![X21 : $i, X22 : $i]:
% 0.76/0.98         (~ (v4_relat_1 @ X21 @ X22)
% 0.76/0.98          | (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.76/0.98          | ~ (v1_relat_1 @ X21))),
% 0.76/0.98      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.76/0.98  thf('14', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.98  thf('15', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf(cc2_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ![B:$i]:
% 0.76/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.98  thf('16', plain,
% 0.76/0.98      (![X19 : $i, X20 : $i]:
% 0.76/0.98         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.76/0.98          | (v1_relat_1 @ X19)
% 0.76/0.98          | ~ (v1_relat_1 @ X20))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.98  thf('17', plain,
% 0.76/0.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['15', '16'])).
% 0.76/0.98  thf(fc6_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.98  thf('18', plain,
% 0.76/0.98      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.98      inference('demod', [status(thm)], ['17', '18'])).
% 0.76/0.98  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.76/0.98      inference('demod', [status(thm)], ['14', '19'])).
% 0.76/0.98  thf(t11_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ C ) =>
% 0.76/0.98       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.76/0.98           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.76/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.76/0.98  thf('21', plain,
% 0.76/0.98      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.76/0.98         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.76/0.98          | ~ (r1_tarski @ (k2_relat_1 @ X40) @ X42)
% 0.76/0.98          | (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.76/0.98          | ~ (v1_relat_1 @ X40))),
% 0.76/0.98      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.76/0.98  thf('22', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ sk_D)
% 0.76/0.98          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.76/0.98          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['20', '21'])).
% 0.76/0.98  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.98      inference('demod', [status(thm)], ['17', '18'])).
% 0.76/0.98  thf('24', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.76/0.98          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.76/0.98      inference('demod', [status(thm)], ['22', '23'])).
% 0.76/0.98  thf('25', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['9', '24'])).
% 0.76/0.98  thf('26', plain,
% 0.76/0.98      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2))))
% 0.76/0.98         <= (~
% 0.76/0.98             ((m1_subset_1 @ sk_D @ 
% 0.76/0.98               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('27', plain,
% 0.76/0.98      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.98  thf('28', plain,
% 0.76/0.98      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)) | 
% 0.76/0.98       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))) | 
% 0.76/0.98       ~ ((v1_funct_1 @ sk_D))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('29', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2))),
% 0.76/0.98      inference('sat_resolution*', [status(thm)], ['4', '27', '28'])).
% 0.76/0.98  thf('30', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_2)),
% 0.76/0.98      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.76/0.98  thf(d1_funct_2, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_1, axiom,
% 0.76/0.98    (![B:$i,A:$i]:
% 0.76/0.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.98       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.98  thf('31', plain,
% 0.76/0.98      (![X43 : $i, X44 : $i]:
% 0.76/0.98         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.98  thf('32', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['9', '24'])).
% 0.76/0.98  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.98  thf(zf_stmt_3, axiom,
% 0.76/0.98    (![C:$i,B:$i,A:$i]:
% 0.76/0.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.98  thf(zf_stmt_5, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.98  thf('33', plain,
% 0.76/0.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.76/0.98         (~ (zip_tseitin_0 @ X48 @ X49)
% 0.76/0.98          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 0.76/0.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.98  thf('34', plain,
% 0.76/0.98      (((zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A)
% 0.76/0.98        | ~ (zip_tseitin_0 @ sk_C_2 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['32', '33'])).
% 0.76/0.98  thf('35', plain,
% 0.76/0.98      ((((sk_C_2) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['31', '34'])).
% 0.76/0.98  thf('36', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_2)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['9', '24'])).
% 0.76/0.98  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.98  thf('37', plain,
% 0.76/0.98      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.76/0.98         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.76/0.98          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.98  thf('38', plain,
% 0.76/0.98      (((k1_relset_1 @ sk_A @ sk_C_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['36', '37'])).
% 0.76/0.98  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('40', plain,
% 0.76/0.98      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.76/0.98         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 0.76/0.98          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 0.76/0.98          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.98  thf('41', plain,
% 0.76/0.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.76/0.98        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['39', '40'])).
% 0.76/0.98  thf('42', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('43', plain,
% 0.76/0.98      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.76/0.98         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.76/0.98          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.98  thf('44', plain,
% 0.76/0.98      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['42', '43'])).
% 0.76/0.98  thf('45', plain,
% 0.76/0.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.76/0.98      inference('demod', [status(thm)], ['41', '44'])).
% 0.76/0.98  thf('46', plain,
% 0.76/0.98      (![X43 : $i, X44 : $i]:
% 0.76/0.98         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.98  thf('47', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('48', plain,
% 0.76/0.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.76/0.98         (~ (zip_tseitin_0 @ X48 @ X49)
% 0.76/0.98          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 0.76/0.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.98  thf('49', plain,
% 0.76/0.98      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['47', '48'])).
% 0.76/0.98  thf('50', plain,
% 0.76/0.98      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.76/0.98      inference('sup-', [status(thm)], ['46', '49'])).
% 0.76/0.98  thf('51', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('52', plain,
% 0.76/0.98      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.76/0.98      inference('split', [status(esa)], ['51'])).
% 0.76/0.98  thf(t149_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.76/0.98  thf('53', plain,
% 0.76/0.98      (![X27 : $i]:
% 0.76/0.98         (((k9_relat_1 @ X27 @ k1_xboole_0) = (k1_xboole_0))
% 0.76/0.98          | ~ (v1_relat_1 @ X27))),
% 0.76/0.98      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.76/0.98  thf(t88_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.76/0.98  thf('54', plain,
% 0.76/0.98      (![X29 : $i, X30 : $i]:
% 0.76/0.98         ((r1_tarski @ (k7_relat_1 @ X29 @ X30) @ X29) | ~ (v1_relat_1 @ X29))),
% 0.76/0.98      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.76/0.98  thf(t66_xboole_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.76/0.98       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.76/0.98  thf('55', plain,
% 0.76/0.98      (![X11 : $i]: ((r1_xboole_0 @ X11 @ X11) | ((X11) != (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.76/0.98  thf('56', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.76/0.98      inference('simplify', [status(thm)], ['55'])).
% 0.76/0.98  thf(d3_tarski, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/0.98  thf('57', plain,
% 0.76/0.98      (![X1 : $i, X3 : $i]:
% 0.76/0.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.98  thf('58', plain,
% 0.76/0.98      (![X1 : $i, X3 : $i]:
% 0.76/0.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.98  thf(t3_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.76/0.98            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.76/0.98       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.76/0.98            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.76/0.98  thf('59', plain,
% 0.76/0.98      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.76/0.98         (~ (r2_hidden @ X6 @ X4)
% 0.76/0.98          | ~ (r2_hidden @ X6 @ X7)
% 0.76/0.98          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.76/0.98      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.76/0.98  thf('60', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.98         ((r1_tarski @ X0 @ X1)
% 0.76/0.98          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.76/0.98          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.76/0.98      inference('sup-', [status(thm)], ['58', '59'])).
% 0.76/0.98  thf('61', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((r1_tarski @ X0 @ X1)
% 0.76/0.98          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.76/0.98          | (r1_tarski @ X0 @ X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['57', '60'])).
% 0.76/0.98  thf('62', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.76/0.98      inference('simplify', [status(thm)], ['61'])).
% 0.76/0.98  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['56', '62'])).
% 0.76/0.98  thf(d10_xboole_0, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.98  thf('64', plain,
% 0.76/0.98      (![X8 : $i, X10 : $i]:
% 0.76/0.98         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.76/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.98  thf('65', plain,
% 0.76/0.98      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['63', '64'])).
% 0.76/0.98  thf('66', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.98          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['54', '65'])).
% 0.76/0.98  thf(t113_zfmisc_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.98       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.76/0.98  thf('67', plain,
% 0.76/0.98      (![X14 : $i, X15 : $i]:
% 0.76/0.98         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.76/0.98          | ((X14) != (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.76/0.98  thf('68', plain,
% 0.76/0.98      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['67'])).
% 0.76/0.98  thf('69', plain,
% 0.76/0.98      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.98  thf('70', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.76/0.98      inference('sup+', [status(thm)], ['68', '69'])).
% 0.76/0.98  thf('71', plain,
% 0.76/0.98      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['66', '70'])).
% 0.76/0.98  thf(t148_relat_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ B ) =>
% 0.76/0.98       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.76/0.98  thf('72', plain,
% 0.76/0.98      (![X25 : $i, X26 : $i]:
% 0.76/0.98         (((k2_relat_1 @ (k7_relat_1 @ X25 @ X26)) = (k9_relat_1 @ X25 @ X26))
% 0.76/0.98          | ~ (v1_relat_1 @ X25))),
% 0.76/0.98      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.76/0.98  thf(t65_relat_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_relat_1 @ A ) =>
% 0.76/0.98       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.98         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.76/0.98  thf('73', plain,
% 0.76/0.98      (![X28 : $i]:
% 0.76/0.98         (((k2_relat_1 @ X28) != (k1_xboole_0))
% 0.76/0.98          | ((k1_relat_1 @ X28) = (k1_xboole_0))
% 0.76/0.98          | ~ (v1_relat_1 @ X28))),
% 0.76/0.98      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.76/0.98  thf('74', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.76/0.98          | ~ (v1_relat_1 @ X1)
% 0.76/0.98          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.76/0.98          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['72', '73'])).
% 0.76/0.98  thf('75', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.98          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.76/0.98          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.98          | ((k9_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['71', '74'])).
% 0.76/0.98  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.76/0.98      inference('sup+', [status(thm)], ['68', '69'])).
% 0.76/0.98  thf('77', plain,
% 0.76/0.98      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['66', '70'])).
% 0.76/0.98  thf('78', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.76/0.98      inference('sup+', [status(thm)], ['68', '69'])).
% 0.76/0.98  thf('79', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.76/0.98          | ((k9_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.76/0.98  thf('80', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.98        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.98        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['53', '79'])).
% 0.76/0.98  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.76/0.98      inference('sup+', [status(thm)], ['68', '69'])).
% 0.76/0.98  thf('82', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.98        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['80', '81'])).
% 0.76/0.98  thf('83', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['82'])).
% 0.76/0.98  thf('84', plain,
% 0.76/0.98      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.76/0.98         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.76/0.98          | ~ (r1_tarski @ (k2_relat_1 @ X40) @ X42)
% 0.76/0.98          | (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.76/0.98          | ~ (v1_relat_1 @ X40))),
% 0.76/0.98      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.76/0.98  thf('85', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.76/0.98          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.98          | (m1_subset_1 @ k1_xboole_0 @ 
% 0.76/0.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.76/0.98          | ~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['83', '84'])).
% 0.76/0.98  thf('86', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['56', '62'])).
% 0.76/0.98  thf('87', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.76/0.98      inference('sup+', [status(thm)], ['68', '69'])).
% 0.76/0.98  thf('88', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['82'])).
% 0.76/0.98  thf('89', plain,
% 0.76/0.98      (![X28 : $i]:
% 0.76/0.98         (((k1_relat_1 @ X28) != (k1_xboole_0))
% 0.76/0.98          | ((k2_relat_1 @ X28) = (k1_xboole_0))
% 0.76/0.98          | ~ (v1_relat_1 @ X28))),
% 0.76/0.98      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.76/0.98  thf('90', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.98        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.76/0.98        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['88', '89'])).
% 0.76/0.98  thf('91', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.76/0.98      inference('sup+', [status(thm)], ['68', '69'])).
% 0.76/0.98  thf('92', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.98        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['90', '91'])).
% 0.76/0.98  thf('93', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['92'])).
% 0.76/0.98  thf('94', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['56', '62'])).
% 0.76/0.98  thf('95', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.76/0.98      inference('demod', [status(thm)], ['85', '86', '87', '93', '94'])).
% 0.76/0.98  thf('96', plain,
% 0.76/0.98      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.76/0.98         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.76/0.98          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.98  thf('97', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['95', '96'])).
% 0.76/0.98  thf('98', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['82'])).
% 0.76/0.98  thf('99', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['97', '98'])).
% 0.76/0.98  thf('100', plain,
% 0.76/0.98      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.76/0.98         (((X45) != (k1_relset_1 @ X45 @ X46 @ X47))
% 0.76/0.98          | (v1_funct_2 @ X47 @ X45 @ X46)
% 0.76/0.98          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.98  thf('101', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (((X1) != (k1_xboole_0))
% 0.76/0.98          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.76/0.98          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['99', '100'])).
% 0.76/0.98  thf('102', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.76/0.98          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['101'])).
% 0.76/0.98  thf('103', plain,
% 0.76/0.98      (![X43 : $i, X44 : $i]:
% 0.76/0.98         ((zip_tseitin_0 @ X43 @ X44) | ((X44) != (k1_xboole_0)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.98  thf('104', plain, (![X43 : $i]: (zip_tseitin_0 @ X43 @ k1_xboole_0)),
% 0.76/0.98      inference('simplify', [status(thm)], ['103'])).
% 0.76/0.98  thf('105', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.76/0.98      inference('demod', [status(thm)], ['85', '86', '87', '93', '94'])).
% 0.76/0.98  thf('106', plain,
% 0.76/0.98      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.76/0.98         (~ (zip_tseitin_0 @ X48 @ X49)
% 0.76/0.98          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 0.76/0.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.98  thf('107', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.76/0.98      inference('sup-', [status(thm)], ['105', '106'])).
% 0.76/0.98  thf('108', plain,
% 0.76/0.98      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['104', '107'])).
% 0.76/0.98  thf('109', plain,
% 0.76/0.98      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('demod', [status(thm)], ['102', '108'])).
% 0.76/0.98  thf('110', plain,
% 0.76/0.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.98      inference('split', [status(esa)], ['51'])).
% 0.76/0.98  thf('111', plain,
% 0.76/0.98      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_2))
% 0.76/0.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)))),
% 0.76/0.98      inference('split', [status(esa)], ['0'])).
% 0.76/0.98  thf('112', plain,
% 0.76/0.98      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_2))
% 0.76/0.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)) & 
% 0.76/0.98             (((sk_A) = (k1_xboole_0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['110', '111'])).
% 0.76/0.98  thf('113', plain,
% 0.76/0.98      (![X1 : $i, X3 : $i]:
% 0.76/0.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.98  thf('114', plain,
% 0.76/0.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.98      inference('split', [status(esa)], ['51'])).
% 0.76/0.98  thf('115', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('116', plain,
% 0.76/0.98      (((m1_subset_1 @ sk_D @ 
% 0.76/0.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.76/0.98         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.98      inference('sup+', [status(thm)], ['114', '115'])).
% 0.76/0.98  thf(t5_subset, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.76/0.98          ( v1_xboole_0 @ C ) ) ))).
% 0.76/0.98  thf('117', plain,
% 0.76/0.98      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.98         (~ (r2_hidden @ X16 @ X17)
% 0.76/0.98          | ~ (v1_xboole_0 @ X18)
% 0.76/0.98          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t5_subset])).
% 0.76/0.98  thf('118', plain,
% 0.76/0.98      ((![X0 : $i]:
% 0.76/0.98          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 0.76/0.98           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.76/0.98         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['116', '117'])).
% 0.76/0.98  thf('119', plain,
% 0.76/0.98      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['67'])).
% 0.76/0.98  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.98  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.98  thf('121', plain,
% 0.76/0.98      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.98      inference('demod', [status(thm)], ['118', '119', '120'])).
% 0.76/0.98  thf('122', plain,
% 0.76/0.98      ((![X0 : $i]: (r1_tarski @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['113', '121'])).
% 0.76/0.98  thf('123', plain,
% 0.76/0.98      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['63', '64'])).
% 0.76/0.98  thf('124', plain,
% 0.76/0.98      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.98      inference('sup-', [status(thm)], ['122', '123'])).
% 0.76/0.98  thf('125', plain,
% 0.76/0.98      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2))
% 0.76/0.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)) & 
% 0.76/0.98             (((sk_A) = (k1_xboole_0))))),
% 0.76/0.98      inference('demod', [status(thm)], ['112', '124'])).
% 0.76/0.98  thf('126', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_2))),
% 0.76/0.98      inference('sat_resolution*', [status(thm)], ['4', '27', '28'])).
% 0.76/0.98  thf('127', plain,
% 0.76/0.98      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_2))
% 0.76/0.98         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.98      inference('simpl_trail', [status(thm)], ['125', '126'])).
% 0.76/0.98  thf('128', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['109', '127'])).
% 0.76/0.98  thf('129', plain,
% 0.76/0.98      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.76/0.98      inference('split', [status(esa)], ['51'])).
% 0.76/0.98  thf('130', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.76/0.98      inference('sat_resolution*', [status(thm)], ['128', '129'])).
% 0.76/0.98  thf('131', plain, (((sk_B) != (k1_xboole_0))),
% 0.76/0.98      inference('simpl_trail', [status(thm)], ['52', '130'])).
% 0.76/0.98  thf('132', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.76/0.98      inference('simplify_reflect-', [status(thm)], ['50', '131'])).
% 0.76/0.98  thf('133', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.76/0.98      inference('demod', [status(thm)], ['45', '132'])).
% 0.76/0.98  thf('134', plain, (((k1_relset_1 @ sk_A @ sk_C_2 @ sk_D) = (sk_A))),
% 0.76/0.98      inference('demod', [status(thm)], ['38', '133'])).
% 0.76/0.98  thf('135', plain,
% 0.76/0.98      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.76/0.98         (((X45) != (k1_relset_1 @ X45 @ X46 @ X47))
% 0.76/0.98          | (v1_funct_2 @ X47 @ X45 @ X46)
% 0.76/0.98          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.98  thf('136', plain,
% 0.76/0.98      ((((sk_A) != (sk_A))
% 0.76/0.98        | ~ (zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A)
% 0.76/0.98        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_2))),
% 0.76/0.98      inference('sup-', [status(thm)], ['134', '135'])).
% 0.76/0.98  thf('137', plain,
% 0.76/0.98      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_2)
% 0.76/0.98        | ~ (zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A))),
% 0.76/0.98      inference('simplify', [status(thm)], ['136'])).
% 0.76/0.98  thf('138', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_2)),
% 0.76/0.98      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.76/0.98  thf('139', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C_2 @ sk_A)),
% 0.76/0.98      inference('clc', [status(thm)], ['137', '138'])).
% 0.76/0.98  thf('140', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['35', '139'])).
% 0.76/0.98  thf('141', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 0.76/0.98      inference('demod', [status(thm)], ['30', '140'])).
% 0.76/0.98  thf('142', plain,
% 0.76/0.98      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C_2)),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('143', plain,
% 0.76/0.98      (![X8 : $i, X10 : $i]:
% 0.76/0.98         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.76/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.98  thf('144', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_C_2 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.76/0.98        | ((sk_C_2) = (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['142', '143'])).
% 0.76/0.98  thf('145', plain,
% 0.76/0.98      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.98  thf('146', plain,
% 0.76/0.98      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.98  thf('147', plain,
% 0.76/0.98      ((~ (r1_tarski @ sk_C_2 @ (k2_relat_1 @ sk_D))
% 0.76/0.98        | ((sk_C_2) = (k2_relat_1 @ sk_D)))),
% 0.76/0.98      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.76/0.98  thf('148', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['35', '139'])).
% 0.76/0.98  thf('149', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['56', '62'])).
% 0.76/0.98  thf('150', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['35', '139'])).
% 0.76/0.98  thf('151', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_D))),
% 0.76/0.98      inference('demod', [status(thm)], ['147', '148', '149', '150'])).
% 0.76/0.98  thf('152', plain,
% 0.76/0.98      (![X28 : $i]:
% 0.76/0.98         (((k2_relat_1 @ X28) != (k1_xboole_0))
% 0.76/0.98          | ((k1_relat_1 @ X28) = (k1_xboole_0))
% 0.76/0.98          | ~ (v1_relat_1 @ X28))),
% 0.76/0.98      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.76/0.98  thf('153', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.98        | ~ (v1_relat_1 @ sk_D)
% 0.76/0.98        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['151', '152'])).
% 0.76/0.98  thf('154', plain, ((v1_relat_1 @ sk_D)),
% 0.76/0.98      inference('demod', [status(thm)], ['17', '18'])).
% 0.76/0.98  thf('155', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.76/0.98      inference('demod', [status(thm)], ['45', '132'])).
% 0.76/0.98  thf('156', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.76/0.98  thf('157', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['156'])).
% 0.76/0.98  thf('158', plain, (~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ k1_xboole_0)),
% 0.76/0.98      inference('demod', [status(thm)], ['141', '157'])).
% 0.76/0.98  thf('159', plain,
% 0.76/0.98      (![X1 : $i, X3 : $i]:
% 0.76/0.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.98  thf('160', plain,
% 0.76/0.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.98  thf('161', plain,
% 0.76/0.98      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.98         (~ (r2_hidden @ X16 @ X17)
% 0.76/0.98          | ~ (v1_xboole_0 @ X18)
% 0.76/0.98          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t5_subset])).
% 0.76/0.98  thf('162', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.76/0.98          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.76/0.98      inference('sup-', [status(thm)], ['160', '161'])).
% 0.76/0.98  thf('163', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['156'])).
% 0.76/0.98  thf('164', plain,
% 0.76/0.98      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['67'])).
% 0.76/0.98  thf('165', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.98  thf('166', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)),
% 0.76/0.98      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 0.76/0.98  thf('167', plain, (![X0 : $i]: (r1_tarski @ sk_D @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['159', '166'])).
% 0.76/0.98  thf('168', plain,
% 0.76/0.98      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['63', '64'])).
% 0.76/0.98  thf('169', plain, (((sk_D) = (k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['167', '168'])).
% 0.76/0.98  thf('170', plain,
% 0.76/0.98      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('demod', [status(thm)], ['102', '108'])).
% 0.76/0.98  thf('171', plain, ($false),
% 0.76/0.98      inference('demod', [status(thm)], ['158', '169', '170'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
