%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p22XgvMCjV

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:14 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 723 expanded)
%              Number of leaves         :   42 ( 218 expanded)
%              Depth                    :   21
%              Number of atoms          : 1422 (8580 expanded)
%              Number of equality atoms :  111 ( 621 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t9_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
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
       => ( ( r1_tarski @ B @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_2])).

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
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('26',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X35 )
      | ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','33','34'])).

thf('36',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('41',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('51',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['60','61'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('63',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('64',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('67',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('72',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('74',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['70','74'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('76',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('77',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','77'])).

thf('79',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('83',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('85',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['81','87'])).

thf('89',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('93',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('94',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('97',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('99',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','101'])).

thf('103',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('104',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('105',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('106',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('107',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('111',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('112',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','102','109','110','111'])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['62','112'])).

thf('114',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['53','113'])).

thf('115',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['46','114'])).

thf('116',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','115'])).

thf('117',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('118',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('121',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('122',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('125',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('127',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('134',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','102','109','110','111'])).

thf('135',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('138',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 != k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ( X43 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('139',plain,(
    ! [X42: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X42 @ k1_xboole_0 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('141',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('143',plain,(
    ! [X42: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X42 @ k1_xboole_0 )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['139','141','142'])).

thf('144',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','77'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['137','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','150'])).

thf('152',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ sk_C @ X1 ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('156',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('158',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['140'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('159',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('160',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('162',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['157','162'])).

thf('164',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['156','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','164'])).

thf('166',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['62','112'])).

thf('167',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['122','167'])).

thf('169',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['119','168'])).

thf('170',plain,(
    $false ),
    inference(demod,[status(thm)],['36','169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p22XgvMCjV
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.16/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.16/1.35  % Solved by: fo/fo7.sh
% 1.16/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.16/1.35  % done 1408 iterations in 0.840s
% 1.16/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.16/1.35  % SZS output start Refutation
% 1.16/1.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.16/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.16/1.35  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.16/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.16/1.35  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.16/1.35  thf(sk_D_type, type, sk_D: $i).
% 1.16/1.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.16/1.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.16/1.35  thf(sk_C_type, type, sk_C: $i).
% 1.16/1.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.16/1.35  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.16/1.35  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.16/1.35  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.16/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.16/1.35  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.16/1.35  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.16/1.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.16/1.35  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.16/1.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.16/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.16/1.35  thf(t9_funct_2, conjecture,
% 1.16/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.16/1.35     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.16/1.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.16/1.35       ( ( r1_tarski @ B @ C ) =>
% 1.16/1.35         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.16/1.35           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.16/1.35             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.16/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.16/1.35    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.16/1.35        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.16/1.35            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.16/1.35          ( ( r1_tarski @ B @ C ) =>
% 1.16/1.35            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.16/1.35              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.16/1.35                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.16/1.35    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 1.16/1.35  thf('0', plain,
% 1.16/1.35      ((~ (v1_funct_1 @ sk_D)
% 1.16/1.35        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 1.16/1.35        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('1', plain,
% 1.16/1.35      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.16/1.35         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.16/1.35      inference('split', [status(esa)], ['0'])).
% 1.16/1.35  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.16/1.35      inference('split', [status(esa)], ['0'])).
% 1.16/1.35  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 1.16/1.35      inference('sup-', [status(thm)], ['2', '3'])).
% 1.16/1.35  thf('5', plain, ((r1_tarski @ sk_B @ sk_C)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('6', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(cc2_relset_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.35       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.16/1.35  thf('7', plain,
% 1.16/1.35      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.16/1.35         ((v5_relat_1 @ X24 @ X26)
% 1.16/1.35          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.16/1.35      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.16/1.35  thf('8', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 1.16/1.35      inference('sup-', [status(thm)], ['6', '7'])).
% 1.16/1.35  thf(d19_relat_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ B ) =>
% 1.16/1.35       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.16/1.35  thf('9', plain,
% 1.16/1.35      (![X20 : $i, X21 : $i]:
% 1.16/1.35         (~ (v5_relat_1 @ X20 @ X21)
% 1.16/1.35          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 1.16/1.35          | ~ (v1_relat_1 @ X20))),
% 1.16/1.35      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.16/1.35  thf('10', plain,
% 1.16/1.35      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 1.16/1.35      inference('sup-', [status(thm)], ['8', '9'])).
% 1.16/1.35  thf('11', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(cc2_relat_1, axiom,
% 1.16/1.35    (![A:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ A ) =>
% 1.16/1.35       ( ![B:$i]:
% 1.16/1.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.16/1.35  thf('12', plain,
% 1.16/1.35      (![X16 : $i, X17 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.16/1.35          | (v1_relat_1 @ X16)
% 1.16/1.35          | ~ (v1_relat_1 @ X17))),
% 1.16/1.35      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.16/1.35  thf('13', plain,
% 1.16/1.35      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 1.16/1.35      inference('sup-', [status(thm)], ['11', '12'])).
% 1.16/1.35  thf(fc6_relat_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.16/1.35  thf('14', plain,
% 1.16/1.35      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 1.16/1.35      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.16/1.35  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 1.16/1.35      inference('demod', [status(thm)], ['13', '14'])).
% 1.16/1.35  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.16/1.35      inference('demod', [status(thm)], ['10', '15'])).
% 1.16/1.35  thf(t1_xboole_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.16/1.35       ( r1_tarski @ A @ C ) ))).
% 1.16/1.35  thf('17', plain,
% 1.16/1.35      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.16/1.35         (~ (r1_tarski @ X1 @ X2)
% 1.16/1.35          | ~ (r1_tarski @ X2 @ X3)
% 1.16/1.35          | (r1_tarski @ X1 @ X3))),
% 1.16/1.35      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.16/1.35  thf('18', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['16', '17'])).
% 1.16/1.35  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 1.16/1.35      inference('sup-', [status(thm)], ['5', '18'])).
% 1.16/1.35  thf('20', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('21', plain,
% 1.16/1.35      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.16/1.35         ((v4_relat_1 @ X24 @ X25)
% 1.16/1.35          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.16/1.35      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.16/1.35  thf('22', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.16/1.35      inference('sup-', [status(thm)], ['20', '21'])).
% 1.16/1.35  thf(d18_relat_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ B ) =>
% 1.16/1.35       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.16/1.35  thf('23', plain,
% 1.16/1.35      (![X18 : $i, X19 : $i]:
% 1.16/1.35         (~ (v4_relat_1 @ X18 @ X19)
% 1.16/1.35          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.16/1.35          | ~ (v1_relat_1 @ X18))),
% 1.16/1.35      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.16/1.35  thf('24', plain,
% 1.16/1.35      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 1.16/1.35      inference('sup-', [status(thm)], ['22', '23'])).
% 1.16/1.35  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 1.16/1.35      inference('demod', [status(thm)], ['13', '14'])).
% 1.16/1.35  thf('26', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 1.16/1.35      inference('demod', [status(thm)], ['24', '25'])).
% 1.16/1.35  thf(t11_relset_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( v1_relat_1 @ C ) =>
% 1.16/1.35       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.16/1.35           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.16/1.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.16/1.35  thf('27', plain,
% 1.16/1.35      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.16/1.35         (~ (r1_tarski @ (k1_relat_1 @ X33) @ X34)
% 1.16/1.35          | ~ (r1_tarski @ (k2_relat_1 @ X33) @ X35)
% 1.16/1.35          | (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.16/1.35          | ~ (v1_relat_1 @ X33))),
% 1.16/1.35      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.16/1.35  thf('28', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ sk_D)
% 1.16/1.35          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.16/1.35          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['26', '27'])).
% 1.16/1.35  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 1.16/1.35      inference('demod', [status(thm)], ['13', '14'])).
% 1.16/1.35  thf('30', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.16/1.35          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.16/1.35      inference('demod', [status(thm)], ['28', '29'])).
% 1.16/1.35  thf('31', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['19', '30'])).
% 1.16/1.35  thf('32', plain,
% 1.16/1.35      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.16/1.35         <= (~
% 1.16/1.35             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.16/1.35      inference('split', [status(esa)], ['0'])).
% 1.16/1.35  thf('33', plain,
% 1.16/1.35      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['31', '32'])).
% 1.16/1.35  thf('34', plain,
% 1.16/1.35      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 1.16/1.35       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.16/1.35       ~ ((v1_funct_1 @ sk_D))),
% 1.16/1.35      inference('split', [status(esa)], ['0'])).
% 1.16/1.35  thf('35', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.16/1.35      inference('sat_resolution*', [status(thm)], ['4', '33', '34'])).
% 1.16/1.35  thf('36', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 1.16/1.35      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 1.16/1.35  thf('37', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['19', '30'])).
% 1.16/1.35  thf(redefinition_k1_relset_1, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.35       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.16/1.35  thf('38', plain,
% 1.16/1.35      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.16/1.35         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.16/1.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.16/1.35  thf('39', plain,
% 1.16/1.35      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.16/1.35      inference('sup-', [status(thm)], ['37', '38'])).
% 1.16/1.35  thf('40', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(d1_funct_2, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.35       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.16/1.35           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.16/1.35             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.16/1.35         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.16/1.35           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.16/1.35             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.16/1.35  thf(zf_stmt_1, axiom,
% 1.16/1.35    (![C:$i,B:$i,A:$i]:
% 1.16/1.35     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.16/1.35       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.16/1.35  thf('41', plain,
% 1.16/1.35      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.16/1.35         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 1.16/1.35          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 1.16/1.35          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.35  thf('42', plain,
% 1.16/1.35      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 1.16/1.35        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['40', '41'])).
% 1.16/1.35  thf('43', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('44', plain,
% 1.16/1.35      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.16/1.35         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.16/1.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.16/1.35  thf('45', plain,
% 1.16/1.35      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.16/1.35      inference('sup-', [status(thm)], ['43', '44'])).
% 1.16/1.35  thf('46', plain,
% 1.16/1.35      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.16/1.35      inference('demod', [status(thm)], ['42', '45'])).
% 1.16/1.35  thf(zf_stmt_2, axiom,
% 1.16/1.35    (![B:$i,A:$i]:
% 1.16/1.35     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.16/1.35       ( zip_tseitin_0 @ B @ A ) ))).
% 1.16/1.35  thf('47', plain,
% 1.16/1.35      (![X36 : $i, X37 : $i]:
% 1.16/1.35         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.16/1.35  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.16/1.35  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.35      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.35  thf('49', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.16/1.35      inference('sup+', [status(thm)], ['47', '48'])).
% 1.16/1.35  thf('50', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.16/1.35  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.16/1.35  thf(zf_stmt_5, axiom,
% 1.16/1.35    (![A:$i,B:$i,C:$i]:
% 1.16/1.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.16/1.35       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.16/1.35         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.16/1.35           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.16/1.35             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.16/1.35  thf('51', plain,
% 1.16/1.35      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.16/1.35         (~ (zip_tseitin_0 @ X41 @ X42)
% 1.16/1.35          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 1.16/1.35          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.16/1.35  thf('52', plain,
% 1.16/1.35      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.16/1.35      inference('sup-', [status(thm)], ['50', '51'])).
% 1.16/1.35  thf('53', plain,
% 1.16/1.35      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 1.16/1.35      inference('sup-', [status(thm)], ['49', '52'])).
% 1.16/1.35  thf(l13_xboole_0, axiom,
% 1.16/1.35    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.16/1.35  thf('54', plain,
% 1.16/1.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.35      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.35  thf('55', plain,
% 1.16/1.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.35      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.35  thf('56', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.16/1.35      inference('sup+', [status(thm)], ['54', '55'])).
% 1.16/1.35  thf('57', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('58', plain,
% 1.16/1.35      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.16/1.35      inference('split', [status(esa)], ['57'])).
% 1.16/1.35  thf('59', plain,
% 1.16/1.35      ((![X0 : $i]:
% 1.16/1.35          (((X0) != (k1_xboole_0))
% 1.16/1.35           | ~ (v1_xboole_0 @ X0)
% 1.16/1.35           | ~ (v1_xboole_0 @ sk_B)))
% 1.16/1.35         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['56', '58'])).
% 1.16/1.35  thf('60', plain,
% 1.16/1.35      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.16/1.35         <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.16/1.35      inference('simplify', [status(thm)], ['59'])).
% 1.16/1.35  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.35      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.35  thf('62', plain,
% 1.16/1.35      ((~ (v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.16/1.35      inference('simplify_reflect+', [status(thm)], ['60', '61'])).
% 1.16/1.35  thf(t4_subset_1, axiom,
% 1.16/1.35    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.16/1.35  thf('63', plain,
% 1.16/1.35      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 1.16/1.35      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.16/1.35  thf('64', plain,
% 1.16/1.35      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.16/1.35         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.16/1.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.16/1.35      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.16/1.35  thf('65', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['63', '64'])).
% 1.16/1.35  thf('66', plain,
% 1.16/1.35      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 1.16/1.35      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.16/1.35  thf('67', plain,
% 1.16/1.35      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.16/1.35         ((v4_relat_1 @ X24 @ X25)
% 1.16/1.35          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.16/1.35      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.16/1.35  thf('68', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 1.16/1.35      inference('sup-', [status(thm)], ['66', '67'])).
% 1.16/1.35  thf('69', plain,
% 1.16/1.35      (![X18 : $i, X19 : $i]:
% 1.16/1.35         (~ (v4_relat_1 @ X18 @ X19)
% 1.16/1.35          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.16/1.35          | ~ (v1_relat_1 @ X18))),
% 1.16/1.35      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.16/1.35  thf('70', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (~ (v1_relat_1 @ k1_xboole_0)
% 1.16/1.35          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['68', '69'])).
% 1.16/1.35  thf(t113_zfmisc_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.16/1.35       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.16/1.35  thf('71', plain,
% 1.16/1.35      (![X7 : $i, X8 : $i]:
% 1.16/1.35         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 1.16/1.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.16/1.35  thf('72', plain,
% 1.16/1.35      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 1.16/1.35      inference('simplify', [status(thm)], ['71'])).
% 1.16/1.35  thf('73', plain,
% 1.16/1.35      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 1.16/1.35      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.16/1.35  thf('74', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.16/1.35      inference('sup+', [status(thm)], ['72', '73'])).
% 1.16/1.35  thf('75', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.16/1.35      inference('demod', [status(thm)], ['70', '74'])).
% 1.16/1.35  thf(t3_xboole_1, axiom,
% 1.16/1.35    (![A:$i]:
% 1.16/1.35     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.16/1.35  thf('76', plain,
% 1.16/1.35      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 1.16/1.35      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.16/1.35  thf('77', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['75', '76'])).
% 1.16/1.35  thf('78', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.35      inference('demod', [status(thm)], ['65', '77'])).
% 1.16/1.35  thf('79', plain,
% 1.16/1.35      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.16/1.35         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 1.16/1.35          | (v1_funct_2 @ X40 @ X38 @ X39)
% 1.16/1.35          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.35  thf('80', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (((X1) != (k1_xboole_0))
% 1.16/1.35          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.16/1.35          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['78', '79'])).
% 1.16/1.35  thf('81', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.16/1.35          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.16/1.35      inference('simplify', [status(thm)], ['80'])).
% 1.16/1.35  thf('82', plain,
% 1.16/1.35      (![X36 : $i, X37 : $i]:
% 1.16/1.35         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.16/1.35  thf('83', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 1.16/1.35      inference('simplify', [status(thm)], ['82'])).
% 1.16/1.35  thf('84', plain,
% 1.16/1.35      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 1.16/1.35      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.16/1.35  thf('85', plain,
% 1.16/1.35      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.16/1.35         (~ (zip_tseitin_0 @ X41 @ X42)
% 1.16/1.35          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 1.16/1.35          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.16/1.35  thf('86', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.16/1.35      inference('sup-', [status(thm)], ['84', '85'])).
% 1.16/1.35  thf('87', plain,
% 1.16/1.35      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.16/1.35      inference('sup-', [status(thm)], ['83', '86'])).
% 1.16/1.35  thf('88', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.16/1.35      inference('demod', [status(thm)], ['81', '87'])).
% 1.16/1.35  thf('89', plain,
% 1.16/1.35      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('split', [status(esa)], ['57'])).
% 1.16/1.35  thf('90', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('91', plain,
% 1.16/1.35      (((m1_subset_1 @ sk_D @ 
% 1.16/1.35         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 1.16/1.35         <= ((((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('sup+', [status(thm)], ['89', '90'])).
% 1.16/1.35  thf('92', plain,
% 1.16/1.35      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 1.16/1.35      inference('simplify', [status(thm)], ['71'])).
% 1.16/1.35  thf('93', plain,
% 1.16/1.35      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.16/1.35         <= ((((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('demod', [status(thm)], ['91', '92'])).
% 1.16/1.35  thf(t3_subset, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.16/1.35  thf('94', plain,
% 1.16/1.35      (![X10 : $i, X11 : $i]:
% 1.16/1.35         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.16/1.35      inference('cnf', [status(esa)], [t3_subset])).
% 1.16/1.35  thf('95', plain,
% 1.16/1.35      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['93', '94'])).
% 1.16/1.35  thf('96', plain,
% 1.16/1.35      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 1.16/1.35      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.16/1.35  thf('97', plain,
% 1.16/1.35      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['95', '96'])).
% 1.16/1.35  thf('98', plain,
% 1.16/1.35      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('split', [status(esa)], ['57'])).
% 1.16/1.35  thf('99', plain,
% 1.16/1.35      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.16/1.35         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.16/1.35      inference('split', [status(esa)], ['0'])).
% 1.16/1.35  thf('100', plain,
% 1.16/1.35      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 1.16/1.35         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['98', '99'])).
% 1.16/1.35  thf('101', plain,
% 1.16/1.35      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 1.16/1.35         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['97', '100'])).
% 1.16/1.35  thf('102', plain,
% 1.16/1.35      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['88', '101'])).
% 1.16/1.35  thf('103', plain,
% 1.16/1.35      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.16/1.35         <= ((((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('demod', [status(thm)], ['91', '92'])).
% 1.16/1.35  thf('104', plain,
% 1.16/1.35      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 1.16/1.35      inference('simplify', [status(thm)], ['71'])).
% 1.16/1.35  thf('105', plain,
% 1.16/1.35      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('split', [status(esa)], ['57'])).
% 1.16/1.35  thf('106', plain,
% 1.16/1.35      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.16/1.35         <= (~
% 1.16/1.35             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.16/1.35      inference('split', [status(esa)], ['0'])).
% 1.16/1.35  thf('107', plain,
% 1.16/1.35      ((~ (m1_subset_1 @ sk_D @ 
% 1.16/1.35           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.16/1.35         <= (~
% 1.16/1.35             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.16/1.35             (((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['105', '106'])).
% 1.16/1.35  thf('108', plain,
% 1.16/1.35      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.16/1.35         <= (~
% 1.16/1.35             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.16/1.35             (((sk_A) = (k1_xboole_0))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['104', '107'])).
% 1.16/1.35  thf('109', plain,
% 1.16/1.35      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.16/1.35       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.16/1.35      inference('sup-', [status(thm)], ['103', '108'])).
% 1.16/1.35  thf('110', plain,
% 1.16/1.35      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.16/1.35       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 1.16/1.35      inference('split', [status(esa)], ['0'])).
% 1.16/1.35  thf('111', plain,
% 1.16/1.35      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.16/1.35      inference('split', [status(esa)], ['57'])).
% 1.16/1.35  thf('112', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 1.16/1.35      inference('sat_resolution*', [status(thm)],
% 1.16/1.35                ['4', '102', '109', '110', '111'])).
% 1.16/1.35  thf('113', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.16/1.35      inference('simpl_trail', [status(thm)], ['62', '112'])).
% 1.16/1.35  thf('114', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 1.16/1.35      inference('clc', [status(thm)], ['53', '113'])).
% 1.16/1.35  thf('115', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.16/1.35      inference('demod', [status(thm)], ['46', '114'])).
% 1.16/1.35  thf('116', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 1.16/1.35      inference('demod', [status(thm)], ['39', '115'])).
% 1.16/1.35  thf('117', plain,
% 1.16/1.35      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.16/1.35         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 1.16/1.35          | (v1_funct_2 @ X40 @ X38 @ X39)
% 1.16/1.35          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.35  thf('118', plain,
% 1.16/1.35      ((((sk_A) != (sk_A))
% 1.16/1.35        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 1.16/1.35        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['116', '117'])).
% 1.16/1.35  thf('119', plain,
% 1.16/1.35      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 1.16/1.35        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 1.16/1.35      inference('simplify', [status(thm)], ['118'])).
% 1.16/1.35  thf('120', plain,
% 1.16/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['19', '30'])).
% 1.16/1.35  thf('121', plain,
% 1.16/1.35      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.16/1.35         (~ (zip_tseitin_0 @ X41 @ X42)
% 1.16/1.35          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 1.16/1.35          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.16/1.35  thf('122', plain,
% 1.16/1.35      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 1.16/1.35      inference('sup-', [status(thm)], ['120', '121'])).
% 1.16/1.35  thf('123', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.16/1.35      inference('sup+', [status(thm)], ['47', '48'])).
% 1.16/1.35  thf('124', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.16/1.35      inference('sup+', [status(thm)], ['47', '48'])).
% 1.16/1.35  thf('125', plain, ((r1_tarski @ sk_B @ sk_C)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('126', plain,
% 1.16/1.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.35      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.35  thf('127', plain,
% 1.16/1.35      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 1.16/1.35      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.16/1.35  thf('128', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (r1_tarski @ X1 @ X0)
% 1.16/1.35          | ~ (v1_xboole_0 @ X0)
% 1.16/1.35          | ((X1) = (k1_xboole_0)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['126', '127'])).
% 1.16/1.35  thf('129', plain, ((((sk_B) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['125', '128'])).
% 1.16/1.35  thf('130', plain,
% 1.16/1.35      (![X0 : $i]: ((zip_tseitin_0 @ sk_C @ X0) | ((sk_B) = (k1_xboole_0)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['124', '129'])).
% 1.16/1.35  thf('131', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.16/1.35      inference('sup-', [status(thm)], ['84', '85'])).
% 1.16/1.35  thf('132', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['130', '131'])).
% 1.16/1.35  thf('133', plain,
% 1.16/1.35      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.16/1.35      inference('split', [status(esa)], ['57'])).
% 1.16/1.35  thf('134', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 1.16/1.35      inference('sat_resolution*', [status(thm)],
% 1.16/1.35                ['4', '102', '109', '110', '111'])).
% 1.16/1.35  thf('135', plain, (((sk_B) != (k1_xboole_0))),
% 1.16/1.35      inference('simpl_trail', [status(thm)], ['133', '134'])).
% 1.16/1.35  thf('136', plain, (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0)),
% 1.16/1.35      inference('simplify_reflect-', [status(thm)], ['132', '135'])).
% 1.16/1.35  thf('137', plain,
% 1.16/1.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.35      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.35  thf('138', plain,
% 1.16/1.35      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.16/1.35         (((X41) != (k1_xboole_0))
% 1.16/1.35          | ((X42) = (k1_xboole_0))
% 1.16/1.35          | (v1_funct_2 @ X43 @ X42 @ X41)
% 1.16/1.35          | ((X43) != (k1_xboole_0))
% 1.16/1.35          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.16/1.35  thf('139', plain,
% 1.16/1.35      (![X42 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 1.16/1.35             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ k1_xboole_0)))
% 1.16/1.35          | (v1_funct_2 @ k1_xboole_0 @ X42 @ k1_xboole_0)
% 1.16/1.35          | ((X42) = (k1_xboole_0)))),
% 1.16/1.35      inference('simplify', [status(thm)], ['138'])).
% 1.16/1.35  thf('140', plain,
% 1.16/1.35      (![X7 : $i, X8 : $i]:
% 1.16/1.35         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 1.16/1.35      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.16/1.35  thf('141', plain,
% 1.16/1.35      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.35      inference('simplify', [status(thm)], ['140'])).
% 1.16/1.35  thf('142', plain,
% 1.16/1.35      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 1.16/1.35      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.16/1.35  thf('143', plain,
% 1.16/1.35      (![X42 : $i]:
% 1.16/1.35         ((v1_funct_2 @ k1_xboole_0 @ X42 @ k1_xboole_0)
% 1.16/1.35          | ((X42) = (k1_xboole_0)))),
% 1.16/1.35      inference('demod', [status(thm)], ['139', '141', '142'])).
% 1.16/1.35  thf('144', plain,
% 1.16/1.35      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.16/1.35         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 1.16/1.35          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 1.16/1.35          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.35  thf('145', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (((X0) = (k1_xboole_0))
% 1.16/1.35          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.16/1.35          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['143', '144'])).
% 1.16/1.35  thf('146', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.35      inference('demod', [status(thm)], ['65', '77'])).
% 1.16/1.35  thf('147', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (((X0) = (k1_xboole_0))
% 1.16/1.35          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.16/1.35          | ((X0) = (k1_xboole_0)))),
% 1.16/1.35      inference('demod', [status(thm)], ['145', '146'])).
% 1.16/1.35  thf('148', plain,
% 1.16/1.35      (![X0 : $i]:
% 1.16/1.35         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.16/1.35          | ((X0) = (k1_xboole_0)))),
% 1.16/1.35      inference('simplify', [status(thm)], ['147'])).
% 1.16/1.35  thf('149', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.16/1.35          | ~ (v1_xboole_0 @ X0)
% 1.16/1.35          | ((X1) = (k1_xboole_0)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['137', '148'])).
% 1.16/1.35  thf('150', plain,
% 1.16/1.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['136', '149'])).
% 1.16/1.35  thf('151', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         ((zip_tseitin_0 @ sk_C @ X1) | ((X0) = (k1_xboole_0)))),
% 1.16/1.35      inference('sup-', [status(thm)], ['123', '150'])).
% 1.16/1.35  thf('152', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.35      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.35  thf('153', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ sk_C @ X1))),
% 1.16/1.35      inference('sup+', [status(thm)], ['151', '152'])).
% 1.16/1.35  thf('154', plain, ((r1_tarski @ sk_B @ sk_C)),
% 1.16/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.35  thf('155', plain,
% 1.16/1.35      (![X10 : $i, X12 : $i]:
% 1.16/1.35         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.16/1.35      inference('cnf', [status(esa)], [t3_subset])).
% 1.16/1.35  thf('156', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['154', '155'])).
% 1.16/1.35  thf('157', plain,
% 1.16/1.35      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.35      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.16/1.35  thf('158', plain,
% 1.16/1.35      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.35      inference('simplify', [status(thm)], ['140'])).
% 1.16/1.35  thf(cc4_relset_1, axiom,
% 1.16/1.35    (![A:$i,B:$i]:
% 1.16/1.35     ( ( v1_xboole_0 @ A ) =>
% 1.16/1.35       ( ![C:$i]:
% 1.16/1.35         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.16/1.35           ( v1_xboole_0 @ C ) ) ) ))).
% 1.16/1.35  thf('159', plain,
% 1.16/1.35      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.16/1.35         (~ (v1_xboole_0 @ X27)
% 1.16/1.35          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 1.16/1.35          | (v1_xboole_0 @ X28))),
% 1.16/1.35      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.16/1.35  thf('160', plain,
% 1.16/1.35      (![X1 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.16/1.35          | (v1_xboole_0 @ X1)
% 1.16/1.35          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.16/1.35      inference('sup-', [status(thm)], ['158', '159'])).
% 1.16/1.35  thf('161', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.35      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.16/1.35  thf('162', plain,
% 1.16/1.35      (![X1 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.16/1.35          | (v1_xboole_0 @ X1))),
% 1.16/1.35      inference('demod', [status(thm)], ['160', '161'])).
% 1.16/1.35  thf('163', plain,
% 1.16/1.35      (![X0 : $i, X1 : $i]:
% 1.16/1.35         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.16/1.35          | ~ (v1_xboole_0 @ X0)
% 1.16/1.35          | (v1_xboole_0 @ X1))),
% 1.16/1.35      inference('sup-', [status(thm)], ['157', '162'])).
% 1.16/1.35  thf('164', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_C))),
% 1.16/1.35      inference('sup-', [status(thm)], ['156', '163'])).
% 1.16/1.35  thf('165', plain,
% 1.16/1.35      (![X0 : $i]: ((zip_tseitin_0 @ sk_C @ X0) | (v1_xboole_0 @ sk_B))),
% 1.16/1.35      inference('sup-', [status(thm)], ['153', '164'])).
% 1.16/1.35  thf('166', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.16/1.35      inference('simpl_trail', [status(thm)], ['62', '112'])).
% 1.16/1.35  thf('167', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 1.16/1.35      inference('clc', [status(thm)], ['165', '166'])).
% 1.16/1.35  thf('168', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 1.16/1.35      inference('demod', [status(thm)], ['122', '167'])).
% 1.16/1.35  thf('169', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 1.16/1.35      inference('demod', [status(thm)], ['119', '168'])).
% 1.16/1.35  thf('170', plain, ($false), inference('demod', [status(thm)], ['36', '169'])).
% 1.16/1.35  
% 1.16/1.35  % SZS output end Refutation
% 1.16/1.35  
% 1.20/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
