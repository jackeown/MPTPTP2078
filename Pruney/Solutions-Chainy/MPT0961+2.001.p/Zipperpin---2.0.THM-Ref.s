%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oilrYiMEpZ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:38 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 344 expanded)
%              Number of leaves         :   43 ( 115 expanded)
%              Depth                    :   13
%              Number of atoms          :  796 (3574 expanded)
%              Number of equality atoms :   45 ( 101 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( ( r1_tarski @ X19 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','11','12'])).

thf('14',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

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

thf('15',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('17',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42
       != ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X20: $i] :
      ( ( ( k2_relat_1 @ X20 )
       != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('41',plain,(
    ! [X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('45',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','48'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('52',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X39 ) ) )
      | ( v1_partfun1 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_partfun1 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X1: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','48'])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('65',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('66',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','63','64','65'])).

thf('67',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('68',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_partfun1 @ X34 @ X35 )
      | ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['32','38','39','49','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oilrYiMEpZ
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:03:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 259 iterations in 0.244s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.68  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.46/0.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.68  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(t3_funct_2, conjecture,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.68       ( ( v1_funct_1 @ A ) & 
% 0.46/0.68         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.46/0.68         ( m1_subset_1 @
% 0.46/0.68           A @ 
% 0.46/0.68           ( k1_zfmisc_1 @
% 0.46/0.68             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i]:
% 0.46/0.68        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.68          ( ( v1_funct_1 @ A ) & 
% 0.46/0.68            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.46/0.68            ( m1_subset_1 @
% 0.46/0.68              A @ 
% 0.46/0.68              ( k1_zfmisc_1 @
% 0.46/0.68                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      ((~ (v1_funct_1 @ sk_A)
% 0.46/0.68        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.46/0.68        | ~ (m1_subset_1 @ sk_A @ 
% 0.46/0.68             (k1_zfmisc_1 @ 
% 0.46/0.68              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.46/0.68         <= (~
% 0.46/0.68             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.68  thf(t21_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) =>
% 0.46/0.68       ( r1_tarski @
% 0.46/0.68         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X19 : $i]:
% 0.46/0.68         ((r1_tarski @ X19 @ 
% 0.46/0.68           (k2_zfmisc_1 @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19)))
% 0.46/0.68          | ~ (v1_relat_1 @ X19))),
% 0.46/0.68      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.46/0.68  thf(t3_subset, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      (![X5 : $i, X7 : $i]:
% 0.46/0.68         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0)
% 0.46/0.68          | (m1_subset_1 @ X0 @ 
% 0.46/0.68             (k1_zfmisc_1 @ 
% 0.46/0.68              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      ((~ (m1_subset_1 @ sk_A @ 
% 0.46/0.68           (k1_zfmisc_1 @ 
% 0.46/0.68            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.46/0.68         <= (~
% 0.46/0.68             ((m1_subset_1 @ sk_A @ 
% 0.46/0.68               (k1_zfmisc_1 @ 
% 0.46/0.68                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      ((~ (v1_relat_1 @ sk_A))
% 0.46/0.68         <= (~
% 0.46/0.68             ((m1_subset_1 @ sk_A @ 
% 0.46/0.68               (k1_zfmisc_1 @ 
% 0.46/0.68                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.68  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (((m1_subset_1 @ sk_A @ 
% 0.46/0.68         (k1_zfmisc_1 @ 
% 0.46/0.68          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.46/0.68      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.46/0.68       ~
% 0.46/0.68       ((m1_subset_1 @ sk_A @ 
% 0.46/0.68         (k1_zfmisc_1 @ 
% 0.46/0.68          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.46/0.68       ~ ((v1_funct_1 @ sk_A))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.46/0.68      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.46/0.68      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.46/0.68  thf(d1_funct_2, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_1, axiom,
% 0.46/0.68    (![B:$i,A:$i]:
% 0.46/0.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.68       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (![X40 : $i, X41 : $i]:
% 0.46/0.68         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0)
% 0.46/0.68          | (m1_subset_1 @ X0 @ 
% 0.46/0.68             (k1_zfmisc_1 @ 
% 0.46/0.68              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.68  thf(zf_stmt_3, axiom,
% 0.46/0.68    (![C:$i,B:$i,A:$i]:
% 0.46/0.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.68  thf(zf_stmt_5, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.46/0.68         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.46/0.68          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.46/0.68          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0)
% 0.46/0.68          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.68          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.68          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.68          | ~ (v1_relat_1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['15', '18'])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0)
% 0.46/0.68          | (m1_subset_1 @ X0 @ 
% 0.46/0.68             (k1_zfmisc_1 @ 
% 0.46/0.68              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.68         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.46/0.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0)
% 0.46/0.68          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.46/0.68              = (k1_relat_1 @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.46/0.68         (((X42) != (k1_relset_1 @ X42 @ X43 @ X44))
% 0.46/0.68          | (v1_funct_2 @ X44 @ X42 @ X43)
% 0.46/0.68          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.46/0.68          | ~ (v1_relat_1 @ X0)
% 0.46/0.68          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.68          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.68          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.68          | ~ (v1_relat_1 @ X0))),
% 0.46/0.68      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0)
% 0.46/0.68          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.68          | ~ (v1_relat_1 @ X0)
% 0.46/0.68          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['19', '25'])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.68          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.68          | ~ (v1_relat_1 @ X0))),
% 0.46/0.68      inference('simplify', [status(thm)], ['26'])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.46/0.68      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.46/0.68  thf('29', plain,
% 0.46/0.68      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.68  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('31', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.68  thf('32', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.46/0.68      inference('demod', [status(thm)], ['14', '31'])).
% 0.46/0.68  thf('33', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.68  thf(t64_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) =>
% 0.46/0.68       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.68           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.68         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      (![X20 : $i]:
% 0.46/0.68         (((k2_relat_1 @ X20) != (k1_xboole_0))
% 0.46/0.68          | ((X20) = (k1_xboole_0))
% 0.46/0.68          | ~ (v1_relat_1 @ X20))),
% 0.46/0.68      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.68        | ~ (v1_relat_1 @ sk_A)
% 0.46/0.68        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.68  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('37', plain,
% 0.46/0.68      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.68      inference('simplify', [status(thm)], ['37'])).
% 0.46/0.68  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.68      inference('simplify', [status(thm)], ['37'])).
% 0.46/0.68  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t110_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) =>
% 0.46/0.68       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.68  thf('41', plain,
% 0.46/0.68      (![X14 : $i]:
% 0.46/0.68         (((k7_relat_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.68          | ~ (v1_relat_1 @ X14))),
% 0.46/0.68      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.46/0.68  thf(t4_subset_1, axiom,
% 0.46/0.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.46/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (![X5 : $i, X6 : $i]:
% 0.46/0.68         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.68  thf('44', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.68      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.68  thf(t91_relat_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ B ) =>
% 0.46/0.68       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.46/0.68         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X24 @ (k1_relat_1 @ X25))
% 0.46/0.68          | ((k1_relat_1 @ (k7_relat_1 @ X25 @ X24)) = (X24))
% 0.46/0.68          | ~ (v1_relat_1 @ X25))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.46/0.68  thf('46', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0)
% 0.46/0.68          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.68          | ~ (v1_relat_1 @ X0)
% 0.46/0.68          | ~ (v1_relat_1 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['41', '46'])).
% 0.46/0.68  thf('48', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0) | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['47'])).
% 0.46/0.68  thf('49', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['40', '48'])).
% 0.46/0.68  thf('50', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['40', '48'])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X0)
% 0.46/0.68          | (m1_subset_1 @ X0 @ 
% 0.46/0.68             (k1_zfmisc_1 @ 
% 0.46/0.68              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf(cc1_partfun1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( v1_xboole_0 @ A ) =>
% 0.46/0.68       ( ![C:$i]:
% 0.46/0.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.69           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.46/0.69  thf('52', plain,
% 0.46/0.69      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.69         (~ (v1_xboole_0 @ X37)
% 0.46/0.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X39)))
% 0.46/0.69          | (v1_partfun1 @ X38 @ X37))),
% 0.46/0.69      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.46/0.69  thf('53', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v1_relat_1 @ X0)
% 0.46/0.69          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.69          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.69  thf('54', plain,
% 0.46/0.69      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.69        | (v1_partfun1 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.46/0.69        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['50', '53'])).
% 0.46/0.69  thf(rc2_subset_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ?[B:$i]:
% 0.46/0.69       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.46/0.69  thf('55', plain, (![X1 : $i]: (v1_xboole_0 @ (sk_B_1 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.46/0.69  thf(existence_m1_subset_1, axiom,
% 0.46/0.69    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.46/0.69  thf('56', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.46/0.69      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.46/0.69  thf(t2_subset, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.69       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.69  thf('57', plain,
% 0.46/0.69      (![X3 : $i, X4 : $i]:
% 0.46/0.69         ((r2_hidden @ X3 @ X4)
% 0.46/0.69          | (v1_xboole_0 @ X4)
% 0.46/0.69          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.46/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.69  thf('58', plain,
% 0.46/0.69      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.69  thf('59', plain,
% 0.46/0.69      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.69  thf(t5_subset, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.69          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.69  thf('60', plain,
% 0.46/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X11 @ X12)
% 0.46/0.69          | ~ (v1_xboole_0 @ X13)
% 0.46/0.69          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.69  thf('61', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.69  thf('62', plain,
% 0.46/0.69      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['58', '61'])).
% 0.46/0.69  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('sup-', [status(thm)], ['55', '62'])).
% 0.46/0.69  thf('64', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['40', '48'])).
% 0.46/0.69  thf(t45_ordinal1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.46/0.69       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.46/0.69  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.46/0.69  thf('66', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.46/0.69      inference('demod', [status(thm)], ['54', '63', '64', '65'])).
% 0.46/0.69  thf('67', plain,
% 0.46/0.69      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.69  thf(cc1_funct_2, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.69       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.46/0.69         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.46/0.69  thf('68', plain,
% 0.46/0.69      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.69         (~ (v1_funct_1 @ X34)
% 0.46/0.69          | ~ (v1_partfun1 @ X34 @ X35)
% 0.46/0.69          | (v1_funct_2 @ X34 @ X35 @ X36)
% 0.46/0.69          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.46/0.69      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.46/0.69  thf('69', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.46/0.69          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 0.46/0.69          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.69  thf('70', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.46/0.69      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.46/0.69  thf('71', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.46/0.69          | ~ (v1_partfun1 @ k1_xboole_0 @ X1))),
% 0.46/0.69      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.69  thf('72', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.69      inference('sup-', [status(thm)], ['66', '71'])).
% 0.46/0.69  thf('73', plain, ($false),
% 0.46/0.69      inference('demod', [status(thm)], ['32', '38', '39', '49', '72'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.53/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
