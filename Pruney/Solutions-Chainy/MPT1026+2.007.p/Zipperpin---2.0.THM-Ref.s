%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yxz5htm4ky

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:53 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 738 expanded)
%              Number of leaves         :   33 ( 219 expanded)
%              Depth                    :   18
%              Number of atoms          :  758 (8292 expanded)
%              Number of equality atoms :   20 ( 317 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t121_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 )
   <= ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_C_3 @ ( k1_funct_2 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X47 @ X46 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X47 @ X44 @ X45 ) @ X47 @ X44 @ X45 )
      | ( X46
       != ( k1_funct_2 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X44: $i,X45: $i,X47: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X47 @ X44 @ X45 ) @ X47 @ X44 @ X45 )
      | ~ ( r2_hidden @ X47 @ ( k1_funct_2 @ X45 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_3 @ sk_B_2 @ sk_A ) @ sk_C_3 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_3 @ sk_B_2 @ sk_A ) @ sk_C_3 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X39 = X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C_3
    = ( sk_E_1 @ sk_C_3 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C_3 @ sk_C_3 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_funct_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C_3 )
   <= ~ ( v1_funct_1 @ sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ sk_C_3 @ sk_C_3 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('15',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X27 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ sk_B_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    zip_tseitin_0 @ sk_C_3 @ sk_C_3 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('23',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( ( k1_relat_1 @ X37 )
        = X40 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_0 @ sk_C_3 @ sk_C_3 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_relat_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['13','30','31'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_partfun1 @ X28 @ X29 )
      | ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('36',plain,
    ( ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_3 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('38',plain,
    ( ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('40',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X33 ) ) )
      | ( v1_partfun1 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('41',plain,
    ( ( v1_partfun1 @ sk_C_3 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('43',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_3 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( v1_partfun1 @ X34 @ X35 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( v1_funct_1 @ X34 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_3 ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ ( k2_relat_1 @ sk_C_3 ) )
    | ( v1_partfun1 @ sk_C_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_3 ) )
    | ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ ( k2_relat_1 @ sk_C_3 ) )
    | ( v1_partfun1 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X50: $i] :
      ( ( v1_funct_2 @ X50 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('55',plain,
    ( ( v1_funct_2 @ sk_C_3 @ sk_A @ ( k2_relat_1 @ sk_C_3 ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('57',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('58',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ ( k2_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_3 ) )
    | ( v1_partfun1 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['52','58'])).

thf('60',plain,
    ( ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_3 ) )
    | ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('63',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_3 ) ),
    inference(clc,[status(thm)],['61','62'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('64',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X14: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X16
       != ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X14 ) )
      | ( X18
       != ( k1_funct_1 @ X14 @ X19 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('66',plain,(
    ! [X14: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X19 ) @ ( k2_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_3 ) )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('72',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('73',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('74',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    v1_partfun1 @ sk_C_3 @ sk_A ),
    inference(demod,[status(thm)],['41','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['38','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['33','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yxz5htm4ky
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.62/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.84  % Solved by: fo/fo7.sh
% 0.62/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.84  % done 477 iterations in 0.387s
% 0.62/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.84  % SZS output start Refutation
% 0.62/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.62/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.84  thf(sk_B_type, type, sk_B: $i > $i).
% 0.62/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.62/0.84  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.62/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.62/0.84  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.62/0.84  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.62/0.84  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.62/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.62/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.62/0.84  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.62/0.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.62/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.62/0.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.62/0.84  thf(t121_funct_2, conjecture,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.62/0.84       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.62/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.62/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.84    (~( ![A:$i,B:$i,C:$i]:
% 0.62/0.84        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.62/0.84          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.62/0.84            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.62/0.84    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.62/0.84  thf('0', plain,
% 0.62/0.84      ((~ (v1_funct_1 @ sk_C_3)
% 0.62/0.84        | ~ (v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2)
% 0.62/0.84        | ~ (m1_subset_1 @ sk_C_3 @ 
% 0.62/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('1', plain,
% 0.62/0.84      ((~ (v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2))
% 0.62/0.84         <= (~ ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2)))),
% 0.62/0.84      inference('split', [status(esa)], ['0'])).
% 0.62/0.84  thf('2', plain, ((r2_hidden @ sk_C_3 @ (k1_funct_2 @ sk_A @ sk_B_2))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(d2_funct_2, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.62/0.84       ( ![D:$i]:
% 0.62/0.84         ( ( r2_hidden @ D @ C ) <=>
% 0.62/0.84           ( ?[E:$i]:
% 0.62/0.84             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.62/0.84               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.62/0.84               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.62/0.84  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.62/0.84  thf(zf_stmt_2, axiom,
% 0.62/0.84    (![E:$i,D:$i,B:$i,A:$i]:
% 0.62/0.84     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.62/0.84       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.62/0.84         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.62/0.84         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.62/0.84  thf(zf_stmt_3, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.62/0.84       ( ![D:$i]:
% 0.62/0.84         ( ( r2_hidden @ D @ C ) <=>
% 0.62/0.84           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.62/0.84  thf('3', plain,
% 0.62/0.84      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.62/0.84         (~ (r2_hidden @ X47 @ X46)
% 0.62/0.84          | (zip_tseitin_0 @ (sk_E_1 @ X47 @ X44 @ X45) @ X47 @ X44 @ X45)
% 0.62/0.84          | ((X46) != (k1_funct_2 @ X45 @ X44)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.62/0.84  thf('4', plain,
% 0.62/0.84      (![X44 : $i, X45 : $i, X47 : $i]:
% 0.62/0.84         ((zip_tseitin_0 @ (sk_E_1 @ X47 @ X44 @ X45) @ X47 @ X44 @ X45)
% 0.62/0.84          | ~ (r2_hidden @ X47 @ (k1_funct_2 @ X45 @ X44)))),
% 0.62/0.84      inference('simplify', [status(thm)], ['3'])).
% 0.62/0.84  thf('5', plain,
% 0.62/0.84      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_3 @ sk_B_2 @ sk_A) @ sk_C_3 @ sk_B_2 @ 
% 0.62/0.84        sk_A)),
% 0.62/0.84      inference('sup-', [status(thm)], ['2', '4'])).
% 0.62/0.84  thf('6', plain,
% 0.62/0.84      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_3 @ sk_B_2 @ sk_A) @ sk_C_3 @ sk_B_2 @ 
% 0.62/0.84        sk_A)),
% 0.62/0.84      inference('sup-', [status(thm)], ['2', '4'])).
% 0.62/0.84  thf('7', plain,
% 0.62/0.84      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.62/0.84         (((X39) = (X37)) | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.62/0.84  thf('8', plain, (((sk_C_3) = (sk_E_1 @ sk_C_3 @ sk_B_2 @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.62/0.84  thf('9', plain, ((zip_tseitin_0 @ sk_C_3 @ sk_C_3 @ sk_B_2 @ sk_A)),
% 0.62/0.84      inference('demod', [status(thm)], ['5', '8'])).
% 0.62/0.84  thf('10', plain,
% 0.62/0.84      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.62/0.84         ((v1_funct_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.62/0.84  thf('11', plain, ((v1_funct_1 @ sk_C_3)),
% 0.62/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.84  thf('12', plain, ((~ (v1_funct_1 @ sk_C_3)) <= (~ ((v1_funct_1 @ sk_C_3)))),
% 0.62/0.84      inference('split', [status(esa)], ['0'])).
% 0.62/0.84  thf('13', plain, (((v1_funct_1 @ sk_C_3))),
% 0.62/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.62/0.84  thf('14', plain, ((zip_tseitin_0 @ sk_C_3 @ sk_C_3 @ sk_B_2 @ sk_A)),
% 0.62/0.84      inference('demod', [status(thm)], ['5', '8'])).
% 0.62/0.84  thf('15', plain,
% 0.62/0.84      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.62/0.84         ((r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 0.62/0.84          | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.62/0.84  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_B_2)),
% 0.62/0.84      inference('sup-', [status(thm)], ['14', '15'])).
% 0.62/0.84  thf(d10_xboole_0, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.84  thf('17', plain,
% 0.62/0.84      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.62/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.84  thf('18', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.62/0.84      inference('simplify', [status(thm)], ['17'])).
% 0.62/0.84  thf(t11_relset_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( v1_relat_1 @ C ) =>
% 0.62/0.84       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.62/0.84           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.62/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.62/0.84  thf('19', plain,
% 0.62/0.84      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.62/0.84         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.62/0.84          | ~ (r1_tarski @ (k2_relat_1 @ X25) @ X27)
% 0.62/0.84          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.62/0.84          | ~ (v1_relat_1 @ X25))),
% 0.62/0.84      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.62/0.84  thf('20', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         (~ (v1_relat_1 @ X0)
% 0.62/0.84          | (m1_subset_1 @ X0 @ 
% 0.62/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.62/0.84          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['18', '19'])).
% 0.62/0.84  thf('21', plain,
% 0.62/0.84      (((m1_subset_1 @ sk_C_3 @ 
% 0.62/0.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ sk_B_2)))
% 0.62/0.84        | ~ (v1_relat_1 @ sk_C_3))),
% 0.62/0.84      inference('sup-', [status(thm)], ['16', '20'])).
% 0.62/0.84  thf('22', plain, ((zip_tseitin_0 @ sk_C_3 @ sk_C_3 @ sk_B_2 @ sk_A)),
% 0.62/0.84      inference('demod', [status(thm)], ['5', '8'])).
% 0.62/0.84  thf('23', plain,
% 0.62/0.84      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.62/0.84         (((k1_relat_1 @ X37) = (X40))
% 0.62/0.84          | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.62/0.84  thf('24', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['22', '23'])).
% 0.62/0.84  thf('25', plain, ((zip_tseitin_0 @ sk_C_3 @ sk_C_3 @ sk_B_2 @ sk_A)),
% 0.62/0.84      inference('demod', [status(thm)], ['5', '8'])).
% 0.62/0.84  thf('26', plain,
% 0.62/0.84      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.62/0.84         ((v1_relat_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.62/0.84  thf('27', plain, ((v1_relat_1 @ sk_C_3)),
% 0.62/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.62/0.84  thf('28', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.62/0.84      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.62/0.84  thf('29', plain,
% 0.62/0.84      ((~ (m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))
% 0.62/0.84         <= (~
% 0.62/0.84             ((m1_subset_1 @ sk_C_3 @ 
% 0.62/0.84               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))))),
% 0.62/0.84      inference('split', [status(esa)], ['0'])).
% 0.62/0.84  thf('30', plain,
% 0.62/0.84      (((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['28', '29'])).
% 0.62/0.84  thf('31', plain,
% 0.62/0.84      (~ ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2)) | 
% 0.62/0.84       ~
% 0.62/0.84       ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))) | 
% 0.62/0.84       ~ ((v1_funct_1 @ sk_C_3))),
% 0.62/0.84      inference('split', [status(esa)], ['0'])).
% 0.62/0.84  thf('32', plain, (~ ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2))),
% 0.62/0.84      inference('sat_resolution*', [status(thm)], ['13', '30', '31'])).
% 0.62/0.84  thf('33', plain, (~ (v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2)),
% 0.62/0.84      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.62/0.84  thf('34', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.62/0.84      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.62/0.84  thf(cc1_funct_2, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.62/0.84         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.62/0.84  thf('35', plain,
% 0.62/0.84      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.62/0.84         (~ (v1_funct_1 @ X28)
% 0.62/0.84          | ~ (v1_partfun1 @ X28 @ X29)
% 0.62/0.84          | (v1_funct_2 @ X28 @ X29 @ X30)
% 0.62/0.84          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.62/0.84      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.62/0.84  thf('36', plain,
% 0.62/0.84      (((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2)
% 0.62/0.84        | ~ (v1_partfun1 @ sk_C_3 @ sk_A)
% 0.62/0.84        | ~ (v1_funct_1 @ sk_C_3))),
% 0.62/0.84      inference('sup-', [status(thm)], ['34', '35'])).
% 0.62/0.84  thf('37', plain, ((v1_funct_1 @ sk_C_3)),
% 0.62/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.84  thf('38', plain,
% 0.62/0.84      (((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2) | ~ (v1_partfun1 @ sk_C_3 @ sk_A))),
% 0.62/0.84      inference('demod', [status(thm)], ['36', '37'])).
% 0.62/0.84  thf('39', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.62/0.84      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.62/0.84  thf(cc1_partfun1, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( v1_xboole_0 @ A ) =>
% 0.62/0.84       ( ![C:$i]:
% 0.62/0.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.62/0.84  thf('40', plain,
% 0.62/0.84      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.62/0.84         (~ (v1_xboole_0 @ X31)
% 0.62/0.84          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X33)))
% 0.62/0.84          | (v1_partfun1 @ X32 @ X31))),
% 0.62/0.84      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.62/0.84  thf('41', plain, (((v1_partfun1 @ sk_C_3 @ sk_A) | ~ (v1_xboole_0 @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['39', '40'])).
% 0.62/0.84  thf('42', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['22', '23'])).
% 0.62/0.84  thf('43', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.62/0.84      inference('simplify', [status(thm)], ['17'])).
% 0.62/0.84  thf('44', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         (~ (v1_relat_1 @ X0)
% 0.62/0.84          | (m1_subset_1 @ X0 @ 
% 0.62/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.62/0.84          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['18', '19'])).
% 0.62/0.84  thf('45', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((m1_subset_1 @ X0 @ 
% 0.62/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.62/0.84          | ~ (v1_relat_1 @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['43', '44'])).
% 0.62/0.84  thf('46', plain,
% 0.62/0.84      (((m1_subset_1 @ sk_C_3 @ 
% 0.62/0.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_3))))
% 0.62/0.84        | ~ (v1_relat_1 @ sk_C_3))),
% 0.62/0.84      inference('sup+', [status(thm)], ['42', '45'])).
% 0.62/0.84  thf('47', plain, ((v1_relat_1 @ sk_C_3)),
% 0.62/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.62/0.84  thf('48', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_C_3 @ 
% 0.62/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_3))))),
% 0.62/0.84      inference('demod', [status(thm)], ['46', '47'])).
% 0.62/0.84  thf(cc5_funct_2, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.62/0.84       ( ![C:$i]:
% 0.62/0.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.62/0.84             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.62/0.84  thf('49', plain,
% 0.62/0.84      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.62/0.84          | (v1_partfun1 @ X34 @ X35)
% 0.62/0.84          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.62/0.84          | ~ (v1_funct_1 @ X34)
% 0.62/0.84          | (v1_xboole_0 @ X36))),
% 0.62/0.84      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.62/0.84  thf('50', plain,
% 0.62/0.84      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_3))
% 0.62/0.84        | ~ (v1_funct_1 @ sk_C_3)
% 0.62/0.84        | ~ (v1_funct_2 @ sk_C_3 @ sk_A @ (k2_relat_1 @ sk_C_3))
% 0.62/0.84        | (v1_partfun1 @ sk_C_3 @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['48', '49'])).
% 0.62/0.84  thf('51', plain, ((v1_funct_1 @ sk_C_3)),
% 0.62/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.84  thf('52', plain,
% 0.62/0.84      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_3))
% 0.62/0.84        | ~ (v1_funct_2 @ sk_C_3 @ sk_A @ (k2_relat_1 @ sk_C_3))
% 0.62/0.84        | (v1_partfun1 @ sk_C_3 @ sk_A))),
% 0.62/0.84      inference('demod', [status(thm)], ['50', '51'])).
% 0.62/0.84  thf('53', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['22', '23'])).
% 0.62/0.84  thf(t3_funct_2, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.62/0.84       ( ( v1_funct_1 @ A ) & 
% 0.62/0.84         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.62/0.84         ( m1_subset_1 @
% 0.62/0.84           A @ 
% 0.62/0.84           ( k1_zfmisc_1 @
% 0.62/0.84             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.62/0.84  thf('54', plain,
% 0.62/0.84      (![X50 : $i]:
% 0.62/0.84         ((v1_funct_2 @ X50 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))
% 0.62/0.84          | ~ (v1_funct_1 @ X50)
% 0.62/0.84          | ~ (v1_relat_1 @ X50))),
% 0.62/0.84      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.62/0.84  thf('55', plain,
% 0.62/0.84      (((v1_funct_2 @ sk_C_3 @ sk_A @ (k2_relat_1 @ sk_C_3))
% 0.62/0.84        | ~ (v1_relat_1 @ sk_C_3)
% 0.62/0.84        | ~ (v1_funct_1 @ sk_C_3))),
% 0.62/0.84      inference('sup+', [status(thm)], ['53', '54'])).
% 0.62/0.84  thf('56', plain, ((v1_relat_1 @ sk_C_3)),
% 0.62/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.62/0.84  thf('57', plain, ((v1_funct_1 @ sk_C_3)),
% 0.62/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.84  thf('58', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ (k2_relat_1 @ sk_C_3))),
% 0.62/0.84      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.62/0.84  thf('59', plain,
% 0.62/0.84      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_3)) | (v1_partfun1 @ sk_C_3 @ sk_A))),
% 0.62/0.84      inference('demod', [status(thm)], ['52', '58'])).
% 0.62/0.84  thf('60', plain,
% 0.62/0.84      (((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2) | ~ (v1_partfun1 @ sk_C_3 @ sk_A))),
% 0.62/0.84      inference('demod', [status(thm)], ['36', '37'])).
% 0.62/0.84  thf('61', plain,
% 0.62/0.84      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_3))
% 0.62/0.84        | (v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2))),
% 0.62/0.84      inference('sup-', [status(thm)], ['59', '60'])).
% 0.62/0.84  thf('62', plain, (~ (v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2)),
% 0.62/0.84      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.62/0.84  thf('63', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_3))),
% 0.62/0.84      inference('clc', [status(thm)], ['61', '62'])).
% 0.62/0.84  thf(d1_xboole_0, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.84  thf('64', plain,
% 0.62/0.84      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.62/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.84  thf(d5_funct_1, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.62/0.84       ( ![B:$i]:
% 0.62/0.84         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.62/0.84           ( ![C:$i]:
% 0.62/0.84             ( ( r2_hidden @ C @ B ) <=>
% 0.62/0.84               ( ?[D:$i]:
% 0.62/0.84                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.62/0.84                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.62/0.84  thf('65', plain,
% 0.62/0.84      (![X14 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.62/0.84         (((X16) != (k2_relat_1 @ X14))
% 0.62/0.84          | (r2_hidden @ X18 @ X16)
% 0.62/0.84          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X14))
% 0.62/0.84          | ((X18) != (k1_funct_1 @ X14 @ X19))
% 0.62/0.84          | ~ (v1_funct_1 @ X14)
% 0.62/0.84          | ~ (v1_relat_1 @ X14))),
% 0.62/0.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.62/0.84  thf('66', plain,
% 0.62/0.84      (![X14 : $i, X19 : $i]:
% 0.62/0.84         (~ (v1_relat_1 @ X14)
% 0.62/0.84          | ~ (v1_funct_1 @ X14)
% 0.62/0.84          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X14))
% 0.62/0.84          | (r2_hidden @ (k1_funct_1 @ X14 @ X19) @ (k2_relat_1 @ X14)))),
% 0.62/0.84      inference('simplify', [status(thm)], ['65'])).
% 0.62/0.84  thf('67', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.62/0.84          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 0.62/0.84             (k2_relat_1 @ X0))
% 0.62/0.84          | ~ (v1_funct_1 @ X0)
% 0.62/0.84          | ~ (v1_relat_1 @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['64', '66'])).
% 0.62/0.84  thf('68', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.84  thf('69', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         (~ (v1_relat_1 @ X0)
% 0.62/0.84          | ~ (v1_funct_1 @ X0)
% 0.62/0.84          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.62/0.84          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['67', '68'])).
% 0.62/0.84  thf('70', plain,
% 0.62/0.84      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_3))
% 0.62/0.84        | ~ (v1_funct_1 @ sk_C_3)
% 0.62/0.84        | ~ (v1_relat_1 @ sk_C_3))),
% 0.62/0.84      inference('sup-', [status(thm)], ['63', '69'])).
% 0.62/0.84  thf('71', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['22', '23'])).
% 0.62/0.84  thf('72', plain, ((v1_funct_1 @ sk_C_3)),
% 0.62/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.84  thf('73', plain, ((v1_relat_1 @ sk_C_3)),
% 0.62/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.62/0.84  thf('74', plain, ((v1_xboole_0 @ sk_A)),
% 0.62/0.84      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.62/0.84  thf('75', plain, ((v1_partfun1 @ sk_C_3 @ sk_A)),
% 0.62/0.84      inference('demod', [status(thm)], ['41', '74'])).
% 0.62/0.84  thf('76', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_2)),
% 0.62/0.84      inference('demod', [status(thm)], ['38', '75'])).
% 0.62/0.84  thf('77', plain, ($false), inference('demod', [status(thm)], ['33', '76'])).
% 0.62/0.84  
% 0.62/0.84  % SZS output end Refutation
% 0.62/0.84  
% 0.62/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
