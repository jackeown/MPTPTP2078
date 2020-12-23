%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zYQPkhmyHX

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:09 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  169 (2095 expanded)
%              Number of leaves         :   40 ( 609 expanded)
%              Depth                    :   24
%              Number of atoms          : 1111 (28812 expanded)
%              Number of equality atoms :   90 (1573 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X32 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','27','28'])).

thf('30',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('53',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('62',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['60','64'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('66',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','67'])).

thf('69',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('75',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['71','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('80',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('87',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('90',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','90'])).

thf('92',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','27','28'])).

thf('93',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['78','93'])).

thf('95',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('96',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['52','96'])).

thf('98',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['50','97'])).

thf('99',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['45','98'])).

thf('100',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','99'])).

thf('101',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('102',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','29'])).

thf('105',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','105'])).

thf('107',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('109',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('110',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('111',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('112',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','105'])).

thf('114',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('115',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('116',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('117',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','105'])).

thf('118',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('119',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['112','113','115','116','117','118'])).

thf('120',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('121',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['45','98'])).

thf('122',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['112','113','115','116','117','118'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','67'])).

thf('125',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['71','77'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['107','119','125','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zYQPkhmyHX
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:31:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 362 iterations in 0.198s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(t8_funct_2, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.67       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.46/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.67           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.46/0.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.67        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.67            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.67          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.46/0.67            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.67              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.46/0.67                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      ((~ (v1_funct_1 @ sk_D)
% 0.46/0.67        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.46/0.67        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.46/0.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.46/0.67      inference('split', [status(esa)], ['0'])).
% 0.46/0.67  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.46/0.67      inference('split', [status(esa)], ['0'])).
% 0.46/0.67  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('5', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.67         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.46/0.67          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.67  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.46/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.67  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['5', '8'])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(cc2_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.67         ((v4_relat_1 @ X21 @ X22)
% 0.46/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.67  thf('12', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.46/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.67  thf(d18_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ B ) =>
% 0.46/0.67       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      (![X17 : $i, X18 : $i]:
% 0.46/0.67         (~ (v4_relat_1 @ X17 @ X18)
% 0.46/0.67          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.46/0.67          | ~ (v1_relat_1 @ X17))),
% 0.46/0.67      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(cc2_relat_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      (![X15 : $i, X16 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.46/0.67          | (v1_relat_1 @ X15)
% 0.46/0.67          | ~ (v1_relat_1 @ X16))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.46/0.67      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.67  thf(fc6_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.46/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.67  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.67  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.46/0.67      inference('demod', [status(thm)], ['14', '19'])).
% 0.46/0.67  thf(t11_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ C ) =>
% 0.46/0.67       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.46/0.67           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.46/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.67         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.46/0.67          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ X32)
% 0.46/0.67          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.46/0.67          | ~ (v1_relat_1 @ X30))),
% 0.46/0.67      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ sk_D)
% 0.46/0.67          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.67          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.67  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.67          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.46/0.67      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['9', '24'])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.46/0.67         <= (~
% 0.46/0.67             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.46/0.67      inference('split', [status(esa)], ['0'])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.46/0.67       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.46/0.67       ~ ((v1_funct_1 @ sk_D))),
% 0.46/0.67      inference('split', [status(esa)], ['0'])).
% 0.46/0.67  thf('29', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.46/0.67      inference('sat_resolution*', [status(thm)], ['4', '27', '28'])).
% 0.46/0.67  thf('30', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.46/0.67      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.46/0.67  thf(d1_funct_2, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_1, axiom,
% 0.46/0.67    (![B:$i,A:$i]:
% 0.46/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      (![X33 : $i, X34 : $i]:
% 0.46/0.67         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['9', '24'])).
% 0.46/0.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.67  thf(zf_stmt_3, axiom,
% 0.46/0.67    (![C:$i,B:$i,A:$i]:
% 0.46/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.67  thf(zf_stmt_5, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.67         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.46/0.67          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.46/0.67          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['31', '34'])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['9', '24'])).
% 0.46/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.67         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.46/0.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.46/0.67      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.67  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('40', plain,
% 0.46/0.67      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.67         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.46/0.67          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 0.46/0.67          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.67  thf('41', plain,
% 0.46/0.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.46/0.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.67  thf('42', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.67         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.46/0.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.67  thf('44', plain,
% 0.46/0.67      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.46/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.67  thf('45', plain,
% 0.46/0.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.46/0.67      inference('demod', [status(thm)], ['41', '44'])).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      (![X33 : $i, X34 : $i]:
% 0.46/0.67         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('48', plain,
% 0.46/0.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.67         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.46/0.67          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.46/0.67          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.67  thf('49', plain,
% 0.46/0.67      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.67  thf('50', plain,
% 0.46/0.67      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['46', '49'])).
% 0.46/0.67  thf('51', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('52', plain,
% 0.46/0.67      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.46/0.67      inference('split', [status(esa)], ['51'])).
% 0.46/0.67  thf(t4_subset_1, axiom,
% 0.46/0.67    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.67  thf('53', plain,
% 0.46/0.67      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf('54', plain,
% 0.46/0.67      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.67         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.46/0.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.67  thf('55', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.67  thf('56', plain,
% 0.46/0.67      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf('57', plain,
% 0.46/0.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.67         ((v4_relat_1 @ X21 @ X22)
% 0.46/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.46/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.67  thf('58', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.46/0.67      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.67  thf('59', plain,
% 0.46/0.67      (![X17 : $i, X18 : $i]:
% 0.46/0.67         (~ (v4_relat_1 @ X17 @ X18)
% 0.46/0.67          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.46/0.67          | ~ (v1_relat_1 @ X17))),
% 0.46/0.67      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.67  thf('60', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.67          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.67  thf(t113_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.67  thf('61', plain,
% 0.46/0.67      (![X6 : $i, X7 : $i]:
% 0.46/0.67         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.67  thf('62', plain,
% 0.46/0.67      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['61'])).
% 0.46/0.67  thf('63', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.46/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.67  thf('64', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.67      inference('sup+', [status(thm)], ['62', '63'])).
% 0.46/0.67  thf('65', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.46/0.67      inference('demod', [status(thm)], ['60', '64'])).
% 0.46/0.67  thf(t3_xboole_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.67  thf('66', plain,
% 0.46/0.67      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.67  thf('67', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.67  thf('68', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('demod', [status(thm)], ['55', '67'])).
% 0.46/0.67  thf('69', plain,
% 0.46/0.67      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.67         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 0.46/0.67          | (v1_funct_2 @ X37 @ X35 @ X36)
% 0.46/0.67          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.67  thf('70', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((X1) != (k1_xboole_0))
% 0.46/0.67          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.46/0.67          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.67  thf('71', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.67          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['70'])).
% 0.46/0.67  thf('72', plain,
% 0.46/0.67      (![X33 : $i, X34 : $i]:
% 0.46/0.67         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.67  thf('73', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 0.46/0.67      inference('simplify', [status(thm)], ['72'])).
% 0.46/0.67  thf('74', plain,
% 0.46/0.67      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.67  thf('75', plain,
% 0.46/0.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.46/0.67         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.46/0.67          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.46/0.67          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.67  thf('76', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['74', '75'])).
% 0.46/0.67  thf('77', plain,
% 0.46/0.67      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.46/0.67      inference('sup-', [status(thm)], ['73', '76'])).
% 0.46/0.67  thf('78', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.67      inference('demod', [status(thm)], ['71', '77'])).
% 0.46/0.67  thf('79', plain,
% 0.46/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('split', [status(esa)], ['51'])).
% 0.46/0.67  thf('80', plain,
% 0.46/0.67      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.46/0.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.46/0.67      inference('split', [status(esa)], ['0'])).
% 0.46/0.67  thf('81', plain,
% 0.46/0.67      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.46/0.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['79', '80'])).
% 0.46/0.67  thf('82', plain,
% 0.46/0.67      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['61'])).
% 0.46/0.67  thf('83', plain,
% 0.46/0.67      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('split', [status(esa)], ['51'])).
% 0.46/0.67  thf('84', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('85', plain,
% 0.46/0.67      (((m1_subset_1 @ sk_D @ 
% 0.46/0.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.46/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['83', '84'])).
% 0.46/0.67  thf('86', plain,
% 0.46/0.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.46/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['82', '85'])).
% 0.46/0.67  thf(t3_subset, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.67  thf('87', plain,
% 0.46/0.67      (![X9 : $i, X10 : $i]:
% 0.46/0.67         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.67  thf('88', plain,
% 0.46/0.67      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['86', '87'])).
% 0.46/0.67  thf('89', plain,
% 0.46/0.67      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.67  thf('90', plain,
% 0.46/0.67      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['88', '89'])).
% 0.46/0.67  thf('91', plain,
% 0.46/0.67      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.46/0.67         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('demod', [status(thm)], ['81', '90'])).
% 0.46/0.67  thf('92', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.46/0.67      inference('sat_resolution*', [status(thm)], ['4', '27', '28'])).
% 0.46/0.67  thf('93', plain,
% 0.46/0.67      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.46/0.67         <= ((((sk_A) = (k1_xboole_0))))),
% 0.46/0.67      inference('simpl_trail', [status(thm)], ['91', '92'])).
% 0.46/0.67  thf('94', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['78', '93'])).
% 0.46/0.67  thf('95', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.46/0.67      inference('split', [status(esa)], ['51'])).
% 0.46/0.67  thf('96', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.46/0.67      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 0.46/0.67  thf('97', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.67      inference('simpl_trail', [status(thm)], ['52', '96'])).
% 0.46/0.67  thf('98', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.46/0.67      inference('simplify_reflect-', [status(thm)], ['50', '97'])).
% 0.46/0.67  thf('99', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.46/0.67      inference('demod', [status(thm)], ['45', '98'])).
% 0.46/0.67  thf('100', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['38', '99'])).
% 0.46/0.67  thf('101', plain,
% 0.46/0.67      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.67         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 0.46/0.67          | (v1_funct_2 @ X37 @ X35 @ X36)
% 0.46/0.67          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.67  thf('102', plain,
% 0.46/0.67      ((((sk_A) != (sk_A))
% 0.46/0.67        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.46/0.67        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['100', '101'])).
% 0.46/0.67  thf('103', plain,
% 0.46/0.67      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.46/0.67        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.46/0.67      inference('simplify', [status(thm)], ['102'])).
% 0.46/0.67  thf('104', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.46/0.67      inference('simpl_trail', [status(thm)], ['1', '29'])).
% 0.46/0.67  thf('105', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.46/0.67      inference('clc', [status(thm)], ['103', '104'])).
% 0.46/0.67  thf('106', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['35', '105'])).
% 0.46/0.67  thf('107', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 0.46/0.67      inference('demod', [status(thm)], ['30', '106'])).
% 0.46/0.67  thf('108', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['9', '24'])).
% 0.46/0.67  thf('109', plain,
% 0.46/0.67      (![X9 : $i, X10 : $i]:
% 0.46/0.67         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.67  thf('110', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['108', '109'])).
% 0.46/0.67  thf(d10_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.67  thf('111', plain,
% 0.46/0.67      (![X0 : $i, X2 : $i]:
% 0.46/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.67  thf('112', plain,
% 0.46/0.67      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 0.46/0.67        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['110', '111'])).
% 0.46/0.67  thf('113', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['35', '105'])).
% 0.46/0.67  thf('114', plain,
% 0.46/0.67      (![X6 : $i, X7 : $i]:
% 0.46/0.67         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.67  thf('115', plain,
% 0.46/0.67      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['114'])).
% 0.46/0.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.67  thf('116', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.46/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.67  thf('117', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['35', '105'])).
% 0.46/0.67  thf('118', plain,
% 0.46/0.67      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['114'])).
% 0.46/0.67  thf('119', plain, (((k1_xboole_0) = (sk_D))),
% 0.46/0.67      inference('demod', [status(thm)],
% 0.46/0.67                ['112', '113', '115', '116', '117', '118'])).
% 0.46/0.67  thf('120', plain,
% 0.46/0.67      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.46/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.67  thf('121', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.46/0.67      inference('demod', [status(thm)], ['45', '98'])).
% 0.46/0.67  thf('122', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['120', '121'])).
% 0.46/0.67  thf('123', plain, (((k1_xboole_0) = (sk_D))),
% 0.46/0.67      inference('demod', [status(thm)],
% 0.46/0.67                ['112', '113', '115', '116', '117', '118'])).
% 0.46/0.67  thf('124', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('demod', [status(thm)], ['55', '67'])).
% 0.46/0.67  thf('125', plain, (((k1_xboole_0) = (sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.46/0.67  thf('126', plain,
% 0.46/0.67      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.67      inference('demod', [status(thm)], ['71', '77'])).
% 0.46/0.67  thf('127', plain, ($false),
% 0.46/0.67      inference('demod', [status(thm)], ['107', '119', '125', '126'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
