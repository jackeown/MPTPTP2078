%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UXaqEhnDYq

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:54 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  196 (17452 expanded)
%              Number of leaves         :   52 (4915 expanded)
%              Depth                    :   23
%              Number of atoms          : 1244 (198483 expanded)
%              Number of equality atoms :   53 (7906 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i )).

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
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_2 ) ),
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
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X56 @ X55 )
      | ( zip_tseitin_0 @ ( sk_E_2 @ X56 @ X53 @ X54 ) @ X56 @ X53 @ X54 )
      | ( X55
       != ( k1_funct_2 @ X54 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X53: $i,X54: $i,X56: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_2 @ X56 @ X53 @ X54 ) @ X56 @ X53 @ X54 )
      | ~ ( r2_hidden @ X56 @ ( k1_funct_2 @ X54 @ X53 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X48 = X46 )
      | ~ ( zip_tseitin_0 @ X46 @ X48 @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C_1
    = ( sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( v1_funct_1 @ X46 )
      | ~ ( zip_tseitin_0 @ X46 @ X48 @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('15',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ~ ( zip_tseitin_0 @ X46 @ X48 @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('23',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( ( k1_relat_1 @ X46 )
        = X49 )
      | ~ ( zip_tseitin_0 @ X46 @ X48 @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('26',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( v1_relat_1 @ X46 )
      | ~ ( zip_tseitin_0 @ X46 @ X48 @ X47 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['13','30','31'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X59: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X59 ) ) ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( v1_partfun1 @ X43 @ X44 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( v1_funct_1 @ X43 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('44',plain,(
    ! [X59: $i] :
      ( ( v1_funct_2 @ X59 @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X59 ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('45',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('47',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('48',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','48'])).

thf('50',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('53',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_C_1
      = ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_C_1
      = ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1
      = ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','64'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('72',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','72'])).

thf('74',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['65','73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','48'])).

thf('76',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('78',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_partfun1 @ X40 @ X41 )
      | ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('79',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('81',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('83',plain,(
    ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['33','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('87',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','83'])).

thf('88',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','48'])).

thf('91',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('92',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('93',plain,(
    v5_relat_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('95',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X18 @ X17 ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v5_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('99',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('100',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('102',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','104'])).

thf('106',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','83'])).

thf('107',plain,
    ( ( v1_partfun1 @ k1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['86','87'])).

thf('109',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['86','87'])).

thf('110',plain,
    ( ( v1_partfun1 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('112',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','83'])).

thf('113',plain,(
    ~ ( v1_partfun1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['86','87'])).

thf('115',plain,(
    ~ ( v1_partfun1 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('118',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['89','118'])).

thf('120',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_1 @ D @ C @ B @ A ) )
       => ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('121',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( ( k1_relat_1 @ X68 )
       != X67 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X68 @ X69 @ X67 ) @ X68 @ X69 @ X67 )
      | ( zip_tseitin_2 @ X68 @ X69 @ X67 )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( v1_relat_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('122',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v1_relat_1 @ X68 )
      | ~ ( v1_funct_1 @ X68 )
      | ( zip_tseitin_2 @ X68 @ X69 @ ( k1_relat_1 @ X68 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X68 @ X69 @ ( k1_relat_1 @ X68 ) ) @ X68 @ X69 @ ( k1_relat_1 @ X68 ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_2 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['120','122'])).

thf('124',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('126',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( zip_tseitin_1 @ X60 @ X61 @ X62 @ X63 )
      | ( r2_hidden @ X60 @ X63 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X2 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_1 @ X2 @ X1 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('131',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('132',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','83'])).

thf('133',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('135',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('136',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( zip_tseitin_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','129','130','133','138'])).

thf('140',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( v1_funct_2 @ X64 @ X66 @ X65 )
      | ~ ( zip_tseitin_2 @ X64 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('141',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['119','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UXaqEhnDYq
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.79/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/1.03  % Solved by: fo/fo7.sh
% 0.79/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.03  % done 1262 iterations in 0.568s
% 0.79/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/1.03  % SZS output start Refutation
% 0.79/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/1.03  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.79/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.79/1.03  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.79/1.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/1.03  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.79/1.03  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.79/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.79/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/1.03  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.79/1.03  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.79/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/1.03  thf(sk_B_type, type, sk_B: $i > $i).
% 0.79/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.79/1.03  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.79/1.03  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.79/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.79/1.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/1.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/1.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.79/1.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.79/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.79/1.03  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.79/1.03  thf(sk_E_2_type, type, sk_E_2: $i > $i > $i > $i).
% 0.79/1.03  thf(t121_funct_2, conjecture,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.79/1.03       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.79/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.03    (~( ![A:$i,B:$i,C:$i]:
% 0.79/1.03        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.79/1.03          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.03            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.79/1.03    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.79/1.03  thf('0', plain,
% 0.79/1.03      ((~ (v1_funct_1 @ sk_C_1)
% 0.79/1.03        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.79/1.03        | ~ (m1_subset_1 @ sk_C_1 @ 
% 0.79/1.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.03  thf('1', plain,
% 0.79/1.03      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2))
% 0.79/1.03         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)))),
% 0.79/1.03      inference('split', [status(esa)], ['0'])).
% 0.79/1.03  thf('2', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_2))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.03  thf(d2_funct_2, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.79/1.03       ( ![D:$i]:
% 0.79/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.79/1.03           ( ?[E:$i]:
% 0.79/1.03             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.79/1.03               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.79/1.03               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.79/1.03  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.79/1.03  thf(zf_stmt_2, axiom,
% 0.79/1.03    (![E:$i,D:$i,B:$i,A:$i]:
% 0.79/1.03     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.79/1.03       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.79/1.03         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.79/1.03         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.79/1.03  thf(zf_stmt_3, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.79/1.03       ( ![D:$i]:
% 0.79/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.79/1.03           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.79/1.03  thf('3', plain,
% 0.79/1.03      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X56 @ X55)
% 0.79/1.03          | (zip_tseitin_0 @ (sk_E_2 @ X56 @ X53 @ X54) @ X56 @ X53 @ X54)
% 0.79/1.03          | ((X55) != (k1_funct_2 @ X54 @ X53)))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.79/1.03  thf('4', plain,
% 0.79/1.03      (![X53 : $i, X54 : $i, X56 : $i]:
% 0.79/1.03         ((zip_tseitin_0 @ (sk_E_2 @ X56 @ X53 @ X54) @ X56 @ X53 @ X54)
% 0.79/1.03          | ~ (r2_hidden @ X56 @ (k1_funct_2 @ X54 @ X53)))),
% 0.79/1.03      inference('simplify', [status(thm)], ['3'])).
% 0.79/1.03  thf('5', plain,
% 0.79/1.03      ((zip_tseitin_0 @ (sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_C_1 @ sk_B_2 @ 
% 0.79/1.03        sk_A)),
% 0.79/1.03      inference('sup-', [status(thm)], ['2', '4'])).
% 0.79/1.03  thf('6', plain,
% 0.79/1.03      ((zip_tseitin_0 @ (sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_C_1 @ sk_B_2 @ 
% 0.79/1.03        sk_A)),
% 0.79/1.03      inference('sup-', [status(thm)], ['2', '4'])).
% 0.79/1.03  thf('7', plain,
% 0.79/1.03      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.79/1.03         (((X48) = (X46)) | ~ (zip_tseitin_0 @ X46 @ X48 @ X47 @ X49))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.79/1.03  thf('8', plain, (((sk_C_1) = (sk_E_2 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.79/1.03  thf('9', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.79/1.03      inference('demod', [status(thm)], ['5', '8'])).
% 0.79/1.03  thf('10', plain,
% 0.79/1.03      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.79/1.03         ((v1_funct_1 @ X46) | ~ (zip_tseitin_0 @ X46 @ X48 @ X47 @ X49))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.79/1.03  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.79/1.03  thf('12', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 0.79/1.03      inference('split', [status(esa)], ['0'])).
% 0.79/1.03  thf('13', plain, (((v1_funct_1 @ sk_C_1))),
% 0.79/1.03      inference('sup-', [status(thm)], ['11', '12'])).
% 0.79/1.03  thf('14', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.79/1.03      inference('demod', [status(thm)], ['5', '8'])).
% 0.79/1.03  thf('15', plain,
% 0.79/1.03      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.79/1.03         ((r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 0.79/1.03          | ~ (zip_tseitin_0 @ X46 @ X48 @ X47 @ X49))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.79/1.03  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_2)),
% 0.79/1.03      inference('sup-', [status(thm)], ['14', '15'])).
% 0.79/1.03  thf(d10_xboole_0, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.79/1.03  thf('17', plain,
% 0.79/1.03      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.79/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/1.03  thf('18', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.79/1.03      inference('simplify', [status(thm)], ['17'])).
% 0.79/1.03  thf(t11_relset_1, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( v1_relat_1 @ C ) =>
% 0.79/1.03       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.79/1.03           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.79/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.79/1.03  thf('19', plain,
% 0.79/1.03      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.79/1.03         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.79/1.03          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 0.79/1.03          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.79/1.03          | ~ (v1_relat_1 @ X29))),
% 0.79/1.03      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.79/1.03  thf('20', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         (~ (v1_relat_1 @ X0)
% 0.79/1.03          | (m1_subset_1 @ X0 @ 
% 0.79/1.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.79/1.03          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.79/1.03      inference('sup-', [status(thm)], ['18', '19'])).
% 0.79/1.03  thf('21', plain,
% 0.79/1.03      (((m1_subset_1 @ sk_C_1 @ 
% 0.79/1.03         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_2)))
% 0.79/1.03        | ~ (v1_relat_1 @ sk_C_1))),
% 0.79/1.03      inference('sup-', [status(thm)], ['16', '20'])).
% 0.79/1.03  thf('22', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.79/1.03      inference('demod', [status(thm)], ['5', '8'])).
% 0.79/1.03  thf('23', plain,
% 0.79/1.03      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.79/1.03         (((k1_relat_1 @ X46) = (X49))
% 0.79/1.03          | ~ (zip_tseitin_0 @ X46 @ X48 @ X47 @ X49))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.79/1.03  thf('24', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.79/1.03  thf('25', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.79/1.03      inference('demod', [status(thm)], ['5', '8'])).
% 0.79/1.03  thf('26', plain,
% 0.79/1.03      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.79/1.03         ((v1_relat_1 @ X46) | ~ (zip_tseitin_0 @ X46 @ X48 @ X47 @ X49))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.79/1.03  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['25', '26'])).
% 0.79/1.03  thf('28', plain,
% 0.79/1.03      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.79/1.03      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.79/1.03  thf('29', plain,
% 0.79/1.03      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))
% 0.79/1.03         <= (~
% 0.79/1.03             ((m1_subset_1 @ sk_C_1 @ 
% 0.79/1.03               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))))),
% 0.79/1.03      inference('split', [status(esa)], ['0'])).
% 0.79/1.03  thf('30', plain,
% 0.79/1.03      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.79/1.03      inference('sup-', [status(thm)], ['28', '29'])).
% 0.79/1.03  thf('31', plain,
% 0.79/1.03      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)) | 
% 0.79/1.03       ~
% 0.79/1.03       ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))) | 
% 0.79/1.03       ~ ((v1_funct_1 @ sk_C_1))),
% 0.79/1.03      inference('split', [status(esa)], ['0'])).
% 0.79/1.03  thf('32', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2))),
% 0.79/1.03      inference('sat_resolution*', [status(thm)], ['13', '30', '31'])).
% 0.79/1.03  thf('33', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 0.79/1.03      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.79/1.03  thf('34', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.79/1.03  thf(t3_funct_2, axiom,
% 0.79/1.03    (![A:$i]:
% 0.79/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.03       ( ( v1_funct_1 @ A ) & 
% 0.79/1.03         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.79/1.03         ( m1_subset_1 @
% 0.79/1.03           A @ 
% 0.79/1.03           ( k1_zfmisc_1 @
% 0.79/1.03             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.79/1.03  thf('35', plain,
% 0.79/1.03      (![X59 : $i]:
% 0.79/1.03         ((m1_subset_1 @ X59 @ 
% 0.79/1.03           (k1_zfmisc_1 @ 
% 0.79/1.03            (k2_zfmisc_1 @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X59))))
% 0.79/1.03          | ~ (v1_funct_1 @ X59)
% 0.79/1.03          | ~ (v1_relat_1 @ X59))),
% 0.79/1.03      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.79/1.03  thf('36', plain,
% 0.79/1.03      (((m1_subset_1 @ sk_C_1 @ 
% 0.79/1.03         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.79/1.03        | ~ (v1_relat_1 @ sk_C_1)
% 0.79/1.03        | ~ (v1_funct_1 @ sk_C_1))),
% 0.79/1.03      inference('sup+', [status(thm)], ['34', '35'])).
% 0.79/1.03  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['25', '26'])).
% 0.79/1.03  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.79/1.03  thf('39', plain,
% 0.79/1.03      ((m1_subset_1 @ sk_C_1 @ 
% 0.79/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.79/1.03      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.79/1.03  thf(cc5_funct_2, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.79/1.03       ( ![C:$i]:
% 0.79/1.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.03           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.79/1.03             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.79/1.03  thf('40', plain,
% 0.79/1.03      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.79/1.03         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.79/1.03          | (v1_partfun1 @ X43 @ X44)
% 0.79/1.03          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.79/1.03          | ~ (v1_funct_1 @ X43)
% 0.79/1.03          | (v1_xboole_0 @ X45))),
% 0.79/1.03      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.79/1.03  thf('41', plain,
% 0.79/1.03      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.79/1.03        | ~ (v1_funct_1 @ sk_C_1)
% 0.79/1.03        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.79/1.03        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['39', '40'])).
% 0.79/1.03  thf('42', plain, ((v1_funct_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.79/1.03  thf('43', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.79/1.03  thf('44', plain,
% 0.79/1.03      (![X59 : $i]:
% 0.79/1.03         ((v1_funct_2 @ X59 @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X59))
% 0.79/1.03          | ~ (v1_funct_1 @ X59)
% 0.79/1.03          | ~ (v1_relat_1 @ X59))),
% 0.79/1.03      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.79/1.03  thf('45', plain,
% 0.79/1.03      (((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.79/1.03        | ~ (v1_relat_1 @ sk_C_1)
% 0.79/1.03        | ~ (v1_funct_1 @ sk_C_1))),
% 0.79/1.03      inference('sup+', [status(thm)], ['43', '44'])).
% 0.79/1.03  thf('46', plain, ((v1_relat_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['25', '26'])).
% 0.79/1.03  thf('47', plain, ((v1_funct_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.79/1.03  thf('48', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 0.79/1.03      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.79/1.03  thf('49', plain,
% 0.79/1.03      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.79/1.03      inference('demod', [status(thm)], ['41', '42', '48'])).
% 0.79/1.03  thf('50', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.79/1.03      inference('simplify', [status(thm)], ['17'])).
% 0.79/1.03  thf(t3_subset, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.79/1.03  thf('51', plain,
% 0.79/1.03      (![X14 : $i, X16 : $i]:
% 0.79/1.03         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.79/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.79/1.03  thf('52', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['50', '51'])).
% 0.79/1.03  thf(cc4_relset_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( v1_xboole_0 @ A ) =>
% 0.79/1.03       ( ![C:$i]:
% 0.79/1.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.79/1.03           ( v1_xboole_0 @ C ) ) ) ))).
% 0.79/1.03  thf('53', plain,
% 0.79/1.03      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.79/1.03         (~ (v1_xboole_0 @ X26)
% 0.79/1.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.79/1.03          | (v1_xboole_0 @ X27))),
% 0.79/1.03      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.79/1.03  thf('54', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['52', '53'])).
% 0.79/1.03  thf('55', plain,
% 0.79/1.03      ((m1_subset_1 @ sk_C_1 @ 
% 0.79/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.79/1.03      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.79/1.03  thf('56', plain,
% 0.79/1.03      (![X14 : $i, X15 : $i]:
% 0.79/1.03         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.79/1.03  thf('57', plain,
% 0.79/1.03      ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['55', '56'])).
% 0.79/1.03  thf(d3_tarski, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( r1_tarski @ A @ B ) <=>
% 0.79/1.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.79/1.03  thf('58', plain,
% 0.79/1.03      (![X4 : $i, X6 : $i]:
% 0.79/1.03         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.79/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.79/1.03  thf(d1_xboole_0, axiom,
% 0.79/1.03    (![A:$i]:
% 0.79/1.03     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.79/1.03  thf('59', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.79/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.79/1.03  thf('60', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['58', '59'])).
% 0.79/1.03  thf('61', plain,
% 0.79/1.03      (![X7 : $i, X9 : $i]:
% 0.79/1.03         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.79/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/1.03  thf('62', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['60', '61'])).
% 0.79/1.03  thf('63', plain,
% 0.79/1.03      ((((sk_C_1) = (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))
% 0.79/1.03        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.79/1.03      inference('sup-', [status(thm)], ['57', '62'])).
% 0.79/1.03  thf('64', plain,
% 0.79/1.03      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.79/1.03        | ((sk_C_1) = (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.79/1.03      inference('sup-', [status(thm)], ['54', '63'])).
% 0.79/1.03  thf('65', plain,
% 0.79/1.03      (((v1_partfun1 @ sk_C_1 @ sk_A)
% 0.79/1.03        | ((sk_C_1) = (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.79/1.03      inference('sup-', [status(thm)], ['49', '64'])).
% 0.79/1.03  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.79/1.03  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.79/1.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.79/1.03  thf('67', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['58', '59'])).
% 0.79/1.03  thf('68', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['60', '61'])).
% 0.79/1.03  thf('69', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['67', '68'])).
% 0.79/1.03  thf('70', plain,
% 0.79/1.03      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['66', '69'])).
% 0.79/1.03  thf(t113_zfmisc_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.79/1.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.79/1.03  thf('71', plain,
% 0.79/1.03      (![X11 : $i, X12 : $i]:
% 0.79/1.03         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.79/1.03          | ((X12) != (k1_xboole_0)))),
% 0.79/1.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.79/1.03  thf('72', plain,
% 0.79/1.03      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.79/1.03      inference('simplify', [status(thm)], ['71'])).
% 0.79/1.03  thf('73', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.03      inference('sup+', [status(thm)], ['70', '72'])).
% 0.79/1.03  thf('74', plain,
% 0.79/1.03      ((((sk_C_1) = (k1_xboole_0))
% 0.79/1.03        | (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.79/1.03        | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.79/1.03      inference('sup+', [status(thm)], ['65', '73'])).
% 0.79/1.03  thf('75', plain,
% 0.79/1.03      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.79/1.03      inference('demod', [status(thm)], ['41', '42', '48'])).
% 0.79/1.03  thf('76', plain,
% 0.79/1.03      (((v1_partfun1 @ sk_C_1 @ sk_A) | ((sk_C_1) = (k1_xboole_0)))),
% 0.79/1.03      inference('clc', [status(thm)], ['74', '75'])).
% 0.79/1.03  thf('77', plain,
% 0.79/1.03      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.79/1.03      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.79/1.03  thf(cc1_funct_2, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.03       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.79/1.03         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.79/1.03  thf('78', plain,
% 0.79/1.03      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.79/1.03         (~ (v1_funct_1 @ X40)
% 0.79/1.03          | ~ (v1_partfun1 @ X40 @ X41)
% 0.79/1.03          | (v1_funct_2 @ X40 @ X41 @ X42)
% 0.79/1.03          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.79/1.03      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.79/1.03  thf('79', plain,
% 0.79/1.03      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.79/1.03        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.79/1.03        | ~ (v1_funct_1 @ sk_C_1))),
% 0.79/1.03      inference('sup-', [status(thm)], ['77', '78'])).
% 0.79/1.03  thf('80', plain, ((v1_funct_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.79/1.03  thf('81', plain,
% 0.79/1.03      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2) | ~ (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.79/1.03      inference('demod', [status(thm)], ['79', '80'])).
% 0.79/1.03  thf('82', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 0.79/1.03      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.79/1.03  thf('83', plain, (~ (v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.79/1.03      inference('clc', [status(thm)], ['81', '82'])).
% 0.79/1.03  thf('84', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['76', '83'])).
% 0.79/1.03  thf('85', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ sk_B_2)),
% 0.79/1.03      inference('demod', [status(thm)], ['33', '84'])).
% 0.79/1.03  thf('86', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.79/1.03  thf('87', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['76', '83'])).
% 0.79/1.03  thf('88', plain, (((k1_relat_1 @ k1_xboole_0) = (sk_A))),
% 0.79/1.03      inference('demod', [status(thm)], ['86', '87'])).
% 0.79/1.03  thf('89', plain,
% 0.79/1.03      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_B_2)),
% 0.79/1.03      inference('demod', [status(thm)], ['85', '88'])).
% 0.79/1.03  thf('90', plain,
% 0.79/1.03      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.79/1.03      inference('demod', [status(thm)], ['41', '42', '48'])).
% 0.79/1.03  thf('91', plain,
% 0.79/1.03      ((m1_subset_1 @ sk_C_1 @ 
% 0.79/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.79/1.03      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.79/1.03  thf(cc2_relset_1, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.03       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.79/1.03  thf('92', plain,
% 0.79/1.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.79/1.03         ((v5_relat_1 @ X23 @ X25)
% 0.79/1.03          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.79/1.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/1.03  thf('93', plain, ((v5_relat_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1))),
% 0.79/1.03      inference('sup-', [status(thm)], ['91', '92'])).
% 0.79/1.03  thf('94', plain,
% 0.79/1.03      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.79/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.79/1.03  thf(t172_funct_1, axiom,
% 0.79/1.03    (![A:$i,B:$i]:
% 0.79/1.03     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.79/1.03       ( ![C:$i]:
% 0.79/1.03         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.79/1.03           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.79/1.03  thf('95', plain,
% 0.79/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.79/1.03         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.79/1.03          | (r2_hidden @ (k1_funct_1 @ X18 @ X17) @ X19)
% 0.79/1.03          | ~ (v1_funct_1 @ X18)
% 0.79/1.03          | ~ (v5_relat_1 @ X18 @ X19)
% 0.79/1.03          | ~ (v1_relat_1 @ X18))),
% 0.79/1.03      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.79/1.03  thf('96', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]:
% 0.79/1.03         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.79/1.03          | ~ (v1_relat_1 @ X0)
% 0.79/1.03          | ~ (v5_relat_1 @ X0 @ X1)
% 0.79/1.03          | ~ (v1_funct_1 @ X0)
% 0.79/1.03          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ X1))),
% 0.79/1.03      inference('sup-', [status(thm)], ['94', '95'])).
% 0.79/1.03  thf('97', plain,
% 0.79/1.03      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_B @ (k1_relat_1 @ sk_C_1))) @ 
% 0.79/1.03         (k2_relat_1 @ sk_C_1))
% 0.79/1.03        | ~ (v1_funct_1 @ sk_C_1)
% 0.79/1.03        | ~ (v1_relat_1 @ sk_C_1)
% 0.79/1.03        | (v1_xboole_0 @ (k1_relat_1 @ sk_C_1)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['93', '96'])).
% 0.79/1.03  thf('98', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.79/1.03  thf('99', plain, ((v1_funct_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.79/1.03  thf('100', plain, ((v1_relat_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['25', '26'])).
% 0.79/1.03  thf('101', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.79/1.03  thf('102', plain,
% 0.79/1.03      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_B @ sk_A)) @ 
% 0.79/1.03         (k2_relat_1 @ sk_C_1))
% 0.79/1.03        | (v1_xboole_0 @ sk_A))),
% 0.79/1.03      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 0.79/1.03  thf('103', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.79/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.79/1.03  thf('104', plain,
% 0.79/1.03      (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['102', '103'])).
% 0.79/1.03  thf('105', plain, (((v1_partfun1 @ sk_C_1 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.79/1.03      inference('sup-', [status(thm)], ['90', '104'])).
% 0.79/1.03  thf('106', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['76', '83'])).
% 0.79/1.03  thf('107', plain,
% 0.79/1.03      (((v1_partfun1 @ k1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.79/1.03      inference('demod', [status(thm)], ['105', '106'])).
% 0.79/1.03  thf('108', plain, (((k1_relat_1 @ k1_xboole_0) = (sk_A))),
% 0.79/1.03      inference('demod', [status(thm)], ['86', '87'])).
% 0.79/1.03  thf('109', plain, (((k1_relat_1 @ k1_xboole_0) = (sk_A))),
% 0.79/1.03      inference('demod', [status(thm)], ['86', '87'])).
% 0.79/1.03  thf('110', plain,
% 0.79/1.03      (((v1_partfun1 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.79/1.03        | (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0)))),
% 0.79/1.03      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.79/1.03  thf('111', plain, (~ (v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.79/1.03      inference('clc', [status(thm)], ['81', '82'])).
% 0.79/1.03  thf('112', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['76', '83'])).
% 0.79/1.03  thf('113', plain, (~ (v1_partfun1 @ k1_xboole_0 @ sk_A)),
% 0.79/1.03      inference('demod', [status(thm)], ['111', '112'])).
% 0.79/1.03  thf('114', plain, (((k1_relat_1 @ k1_xboole_0) = (sk_A))),
% 0.79/1.03      inference('demod', [status(thm)], ['86', '87'])).
% 0.79/1.03  thf('115', plain,
% 0.79/1.03      (~ (v1_partfun1 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 0.79/1.03      inference('demod', [status(thm)], ['113', '114'])).
% 0.79/1.03  thf('116', plain, ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 0.79/1.03      inference('clc', [status(thm)], ['110', '115'])).
% 0.79/1.03  thf('117', plain,
% 0.79/1.03      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.79/1.03      inference('sup-', [status(thm)], ['66', '69'])).
% 0.79/1.03  thf('118', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['116', '117'])).
% 0.79/1.03  thf('119', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_2)),
% 0.79/1.03      inference('demod', [status(thm)], ['89', '118'])).
% 0.79/1.03  thf('120', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['116', '117'])).
% 0.79/1.03  thf(t5_funct_2, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.79/1.03       ( ( ( ![D:$i]:
% 0.79/1.03             ( ( r2_hidden @ D @ A ) =>
% 0.79/1.03               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.79/1.03           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.79/1.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.03           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.79/1.03  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.79/1.03  thf(zf_stmt_5, axiom,
% 0.79/1.03    (![C:$i,B:$i,A:$i]:
% 0.79/1.03     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.79/1.03       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.79/1.03  thf(zf_stmt_6, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.79/1.03  thf(zf_stmt_7, axiom,
% 0.79/1.03    (![D:$i,C:$i,B:$i,A:$i]:
% 0.79/1.03     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.79/1.03       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.79/1.03  thf(zf_stmt_8, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.79/1.03       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.79/1.03           ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.79/1.03         ( zip_tseitin_2 @ C @ B @ A ) ) ))).
% 0.79/1.03  thf('121', plain,
% 0.79/1.03      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.79/1.03         (((k1_relat_1 @ X68) != (X67))
% 0.79/1.03          | ~ (zip_tseitin_1 @ (sk_D_1 @ X68 @ X69 @ X67) @ X68 @ X69 @ X67)
% 0.79/1.03          | (zip_tseitin_2 @ X68 @ X69 @ X67)
% 0.79/1.03          | ~ (v1_funct_1 @ X68)
% 0.79/1.03          | ~ (v1_relat_1 @ X68))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.79/1.03  thf('122', plain,
% 0.79/1.03      (![X68 : $i, X69 : $i]:
% 0.79/1.03         (~ (v1_relat_1 @ X68)
% 0.79/1.03          | ~ (v1_funct_1 @ X68)
% 0.79/1.03          | (zip_tseitin_2 @ X68 @ X69 @ (k1_relat_1 @ X68))
% 0.79/1.03          | ~ (zip_tseitin_1 @ (sk_D_1 @ X68 @ X69 @ (k1_relat_1 @ X68)) @ 
% 0.79/1.03               X68 @ X69 @ (k1_relat_1 @ X68)))),
% 0.79/1.03      inference('simplify', [status(thm)], ['121'])).
% 0.79/1.03  thf('123', plain,
% 0.79/1.03      (![X0 : $i]:
% 0.79/1.03         (~ (zip_tseitin_1 @ 
% 0.79/1.03             (sk_D_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)) @ 
% 0.79/1.03             k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.79/1.03          | (zip_tseitin_2 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 0.79/1.03          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.79/1.03          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['120', '122'])).
% 0.79/1.03  thf('124', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['116', '117'])).
% 0.79/1.03  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.79/1.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.79/1.03  thf('126', plain,
% 0.79/1.03      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 0.79/1.03         ((zip_tseitin_1 @ X60 @ X61 @ X62 @ X63) | (r2_hidden @ X60 @ X63))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.79/1.03  thf('127', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.79/1.03      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.79/1.03  thf('128', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.79/1.03         ((zip_tseitin_1 @ X1 @ X3 @ X2 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['126', '127'])).
% 0.79/1.03  thf('129', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.03         (zip_tseitin_1 @ X2 @ X1 @ X0 @ k1_xboole_0)),
% 0.79/1.03      inference('sup-', [status(thm)], ['125', '128'])).
% 0.79/1.03  thf('130', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['116', '117'])).
% 0.79/1.03  thf('131', plain, ((v1_funct_1 @ sk_C_1)),
% 0.79/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.79/1.03  thf('132', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['76', '83'])).
% 0.79/1.03  thf('133', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.79/1.03      inference('demod', [status(thm)], ['131', '132'])).
% 0.79/1.03  thf('134', plain,
% 0.79/1.03      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.79/1.03      inference('simplify', [status(thm)], ['71'])).
% 0.79/1.03  thf('135', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['50', '51'])).
% 0.79/1.03  thf(cc1_relset_1, axiom,
% 0.79/1.03    (![A:$i,B:$i,C:$i]:
% 0.79/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.03       ( v1_relat_1 @ C ) ))).
% 0.79/1.03  thf('136', plain,
% 0.79/1.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.79/1.03         ((v1_relat_1 @ X20)
% 0.79/1.03          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.79/1.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.79/1.03  thf('137', plain,
% 0.79/1.03      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 0.79/1.03      inference('sup-', [status(thm)], ['135', '136'])).
% 0.79/1.03  thf('138', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.79/1.03      inference('sup+', [status(thm)], ['134', '137'])).
% 0.79/1.03  thf('139', plain,
% 0.79/1.03      (![X0 : $i]: (zip_tseitin_2 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.79/1.03      inference('demod', [status(thm)],
% 0.79/1.03                ['123', '124', '129', '130', '133', '138'])).
% 0.79/1.03  thf('140', plain,
% 0.79/1.03      (![X64 : $i, X65 : $i, X66 : $i]:
% 0.79/1.03         ((v1_funct_2 @ X64 @ X66 @ X65) | ~ (zip_tseitin_2 @ X64 @ X65 @ X66))),
% 0.79/1.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.79/1.03  thf('141', plain,
% 0.79/1.03      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.79/1.03      inference('sup-', [status(thm)], ['139', '140'])).
% 0.79/1.03  thf('142', plain, ($false), inference('demod', [status(thm)], ['119', '141'])).
% 0.79/1.03  
% 0.79/1.03  % SZS output end Refutation
% 0.79/1.03  
% 0.87/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
