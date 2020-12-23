%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LLt6YhPMo3

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:52 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 713 expanded)
%              Number of leaves         :   38 ( 214 expanded)
%              Depth                    :   17
%              Number of atoms          :  936 (7784 expanded)
%              Number of equality atoms :   16 ( 279 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X32 ) ) )
      | ( v1_partfun1 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_partfun1 @ X2 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_partfun1 @ X27 @ X28 )
      | ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B ) ),
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

thf('21',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X46 @ X45 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X46 @ X43 @ X44 ) @ X46 @ X43 @ X44 )
      | ( X45
       != ( k1_funct_2 @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,(
    ! [X43: $i,X44: $i,X46: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X46 @ X43 @ X44 ) @ X46 @ X43 @ X44 )
      | ~ ( r2_hidden @ X46 @ ( k1_funct_2 @ X44 @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['20','22'])).

thf('25',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X38 = X36 )
      | ~ ( zip_tseitin_0 @ X36 @ X38 @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,
    ( sk_C_1
    = ( sk_E_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_funct_1 @ X36 )
      | ~ ( zip_tseitin_0 @ X36 @ X38 @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('33',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('35',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['23','26'])).

thf('36',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X37 )
      | ~ ( zip_tseitin_0 @ X36 @ X38 @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['23','26'])).

thf('39',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relat_1 @ X36 )
        = X39 )
      | ~ ( zip_tseitin_0 @ X36 @ X38 @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X26 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['23','26'])).

thf('44',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_relat_1 @ X36 )
      | ~ ( zip_tseitin_0 @ X36 @ X38 @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('52',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','50','51'])).

thf('53',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['30','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v4_relat_1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('62',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['54','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(condensation,[status(thm)],['66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['53','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('74',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('78',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( v1_partfun1 @ X33 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('81',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('82',plain,(
    ! [X49: $i] :
      ( ( v1_funct_2 @ X49 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('85',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('86',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('89',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_partfun1 @ X27 @ X28 )
      | ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('90',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('92',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('94',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['33','50','51'])).

thf('95',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['92','95'])).

thf('97',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['87','96'])).

thf('98',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['76','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['68','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LLt6YhPMo3
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.80  % Solved by: fo/fo7.sh
% 0.57/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.80  % done 425 iterations in 0.343s
% 0.57/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.80  % SZS output start Refutation
% 0.57/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.57/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.57/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.57/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.57/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.80  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.57/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.57/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.57/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.57/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.80  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.57/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.57/0.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.57/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.57/0.80  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.57/0.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.57/0.80  thf(d3_tarski, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( r1_tarski @ A @ B ) <=>
% 0.57/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.57/0.80  thf('0', plain,
% 0.57/0.80      (![X1 : $i, X3 : $i]:
% 0.57/0.80         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.57/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.80  thf(d10_xboole_0, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.57/0.80  thf('1', plain,
% 0.57/0.80      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.57/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.80  thf('2', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.57/0.80      inference('simplify', [status(thm)], ['1'])).
% 0.57/0.80  thf(t3_subset, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.57/0.80  thf('3', plain,
% 0.57/0.80      (![X10 : $i, X12 : $i]:
% 0.57/0.80         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.80  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.57/0.80  thf(t5_subset, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.57/0.80          ( v1_xboole_0 @ C ) ) ))).
% 0.57/0.80  thf('5', plain,
% 0.57/0.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.80         (~ (r2_hidden @ X13 @ X14)
% 0.57/0.80          | ~ (v1_xboole_0 @ X15)
% 0.57/0.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.57/0.80      inference('cnf', [status(esa)], [t5_subset])).
% 0.57/0.80  thf('6', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['4', '5'])).
% 0.57/0.80  thf('7', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['0', '6'])).
% 0.57/0.80  thf('8', plain,
% 0.57/0.80      (![X10 : $i, X12 : $i]:
% 0.57/0.80         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.80  thf('9', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.80  thf(cc1_partfun1, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( v1_xboole_0 @ A ) =>
% 0.57/0.80       ( ![C:$i]:
% 0.57/0.80         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.80           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.57/0.80  thf('10', plain,
% 0.57/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X30)
% 0.57/0.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X32)))
% 0.57/0.80          | (v1_partfun1 @ X31 @ X30))),
% 0.57/0.80      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.57/0.80  thf('11', plain,
% 0.57/0.80      (![X1 : $i, X2 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X2) | (v1_partfun1 @ X2 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.57/0.80  thf('12', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.80  thf(cc1_funct_2, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.80       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.57/0.80         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.57/0.80  thf('13', plain,
% 0.57/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.57/0.80         (~ (v1_funct_1 @ X27)
% 0.57/0.80          | ~ (v1_partfun1 @ X27 @ X28)
% 0.57/0.80          | (v1_funct_2 @ X27 @ X28 @ X29)
% 0.57/0.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.57/0.80      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.57/0.80  thf('14', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X2)
% 0.57/0.80          | (v1_funct_2 @ X2 @ X1 @ X0)
% 0.57/0.80          | ~ (v1_partfun1 @ X2 @ X1)
% 0.57/0.80          | ~ (v1_funct_1 @ X2))),
% 0.57/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.57/0.80  thf('15', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X0)
% 0.57/0.80          | ~ (v1_xboole_0 @ X1)
% 0.57/0.80          | ~ (v1_funct_1 @ X1)
% 0.57/0.80          | (v1_funct_2 @ X1 @ X0 @ X2)
% 0.57/0.80          | ~ (v1_xboole_0 @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['11', '14'])).
% 0.57/0.80  thf('16', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.80         ((v1_funct_2 @ X1 @ X0 @ X2)
% 0.57/0.80          | ~ (v1_funct_1 @ X1)
% 0.57/0.80          | ~ (v1_xboole_0 @ X1)
% 0.57/0.80          | ~ (v1_xboole_0 @ X0))),
% 0.57/0.80      inference('simplify', [status(thm)], ['15'])).
% 0.57/0.80  thf(t121_funct_2, conjecture,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.57/0.80       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.57/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.57/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.80    (~( ![A:$i,B:$i,C:$i]:
% 0.57/0.80        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.57/0.80          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.57/0.80            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.57/0.80    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.57/0.80  thf('17', plain,
% 0.57/0.80      ((~ (v1_funct_1 @ sk_C_1)
% 0.57/0.80        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.57/0.80        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf('18', plain,
% 0.57/0.80      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.57/0.80         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.57/0.80      inference('split', [status(esa)], ['17'])).
% 0.57/0.80  thf('19', plain,
% 0.57/0.80      (((~ (v1_xboole_0 @ sk_A)
% 0.57/0.80         | ~ (v1_xboole_0 @ sk_C_1)
% 0.57/0.80         | ~ (v1_funct_1 @ sk_C_1)))
% 0.57/0.80         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['16', '18'])).
% 0.57/0.80  thf('20', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.80  thf(d2_funct_2, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.57/0.80       ( ![D:$i]:
% 0.57/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.57/0.80           ( ?[E:$i]:
% 0.57/0.80             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.57/0.80               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.57/0.80               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.57/0.80  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.57/0.80  thf(zf_stmt_2, axiom,
% 0.57/0.80    (![E:$i,D:$i,B:$i,A:$i]:
% 0.57/0.80     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.57/0.80       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.57/0.80         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.57/0.80         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.57/0.80  thf(zf_stmt_3, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.57/0.80       ( ![D:$i]:
% 0.57/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.57/0.80           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.57/0.80  thf('21', plain,
% 0.57/0.80      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.57/0.80         (~ (r2_hidden @ X46 @ X45)
% 0.57/0.80          | (zip_tseitin_0 @ (sk_E_1 @ X46 @ X43 @ X44) @ X46 @ X43 @ X44)
% 0.57/0.80          | ((X45) != (k1_funct_2 @ X44 @ X43)))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.80  thf('22', plain,
% 0.57/0.80      (![X43 : $i, X44 : $i, X46 : $i]:
% 0.57/0.80         ((zip_tseitin_0 @ (sk_E_1 @ X46 @ X43 @ X44) @ X46 @ X43 @ X44)
% 0.57/0.80          | ~ (r2_hidden @ X46 @ (k1_funct_2 @ X44 @ X43)))),
% 0.57/0.80      inference('simplify', [status(thm)], ['21'])).
% 0.57/0.80  thf('23', plain,
% 0.57/0.80      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1 @ sk_B @ sk_A)),
% 0.57/0.80      inference('sup-', [status(thm)], ['20', '22'])).
% 0.57/0.80  thf('24', plain,
% 0.57/0.80      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1 @ sk_B @ sk_A)),
% 0.57/0.80      inference('sup-', [status(thm)], ['20', '22'])).
% 0.57/0.80  thf('25', plain,
% 0.57/0.80      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.57/0.80         (((X38) = (X36)) | ~ (zip_tseitin_0 @ X36 @ X38 @ X37 @ X39))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.80  thf('26', plain, (((sk_C_1) = (sk_E_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.57/0.80      inference('sup-', [status(thm)], ['24', '25'])).
% 0.57/0.80  thf('27', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.57/0.80      inference('demod', [status(thm)], ['23', '26'])).
% 0.57/0.80  thf('28', plain,
% 0.57/0.80      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.57/0.80         ((v1_funct_1 @ X36) | ~ (zip_tseitin_0 @ X36 @ X38 @ X37 @ X39))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.80  thf('29', plain, ((v1_funct_1 @ sk_C_1)),
% 0.57/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.80  thf('30', plain,
% 0.57/0.80      (((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C_1)))
% 0.57/0.80         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.57/0.80      inference('demod', [status(thm)], ['19', '29'])).
% 0.57/0.80  thf('31', plain, ((v1_funct_1 @ sk_C_1)),
% 0.57/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.80  thf('32', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 0.57/0.80      inference('split', [status(esa)], ['17'])).
% 0.57/0.80  thf('33', plain, (((v1_funct_1 @ sk_C_1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['31', '32'])).
% 0.57/0.80  thf('34', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.57/0.80      inference('simplify', [status(thm)], ['1'])).
% 0.57/0.80  thf('35', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.57/0.80      inference('demod', [status(thm)], ['23', '26'])).
% 0.57/0.80  thf('36', plain,
% 0.57/0.80      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.57/0.80         ((r1_tarski @ (k2_relat_1 @ X36) @ X37)
% 0.57/0.80          | ~ (zip_tseitin_0 @ X36 @ X38 @ X37 @ X39))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.80  thf('37', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.57/0.80      inference('sup-', [status(thm)], ['35', '36'])).
% 0.57/0.80  thf('38', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.57/0.80      inference('demod', [status(thm)], ['23', '26'])).
% 0.57/0.80  thf('39', plain,
% 0.57/0.80      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.57/0.80         (((k1_relat_1 @ X36) = (X39))
% 0.57/0.80          | ~ (zip_tseitin_0 @ X36 @ X38 @ X37 @ X39))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.80  thf('40', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.57/0.80      inference('sup-', [status(thm)], ['38', '39'])).
% 0.57/0.80  thf(t11_relset_1, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( v1_relat_1 @ C ) =>
% 0.57/0.80       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.57/0.80           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.57/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.57/0.80  thf('41', plain,
% 0.57/0.80      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.57/0.80         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.57/0.80          | ~ (r1_tarski @ (k2_relat_1 @ X24) @ X26)
% 0.57/0.80          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.57/0.80          | ~ (v1_relat_1 @ X24))),
% 0.57/0.80      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.57/0.80  thf('42', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (r1_tarski @ sk_A @ X0)
% 0.57/0.80          | ~ (v1_relat_1 @ sk_C_1)
% 0.57/0.80          | (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.57/0.80          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['40', '41'])).
% 0.57/0.80  thf('43', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.57/0.80      inference('demod', [status(thm)], ['23', '26'])).
% 0.57/0.80  thf('44', plain,
% 0.57/0.80      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.57/0.80         ((v1_relat_1 @ X36) | ~ (zip_tseitin_0 @ X36 @ X38 @ X37 @ X39))),
% 0.57/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.80  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 0.57/0.80      inference('sup-', [status(thm)], ['43', '44'])).
% 0.57/0.80  thf('46', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (r1_tarski @ sk_A @ X0)
% 0.57/0.80          | (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.57/0.80          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ X1))),
% 0.57/0.80      inference('demod', [status(thm)], ['42', '45'])).
% 0.57/0.80  thf('47', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.57/0.80          | ~ (r1_tarski @ sk_A @ X0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['37', '46'])).
% 0.57/0.80  thf('48', plain,
% 0.57/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['34', '47'])).
% 0.57/0.80  thf('49', plain,
% 0.57/0.80      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.57/0.80         <= (~
% 0.57/0.80             ((m1_subset_1 @ sk_C_1 @ 
% 0.57/0.80               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.57/0.80      inference('split', [status(esa)], ['17'])).
% 0.57/0.80  thf('50', plain,
% 0.57/0.80      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.57/0.80      inference('sup-', [status(thm)], ['48', '49'])).
% 0.57/0.80  thf('51', plain,
% 0.57/0.80      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.57/0.80       ~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.57/0.80       ~ ((v1_funct_1 @ sk_C_1))),
% 0.57/0.80      inference('split', [status(esa)], ['17'])).
% 0.57/0.80  thf('52', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.57/0.80      inference('sat_resolution*', [status(thm)], ['33', '50', '51'])).
% 0.57/0.80  thf('53', plain, ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.57/0.80      inference('simpl_trail', [status(thm)], ['30', '52'])).
% 0.57/0.80  thf('54', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.57/0.80      inference('sup-', [status(thm)], ['38', '39'])).
% 0.57/0.80  thf('55', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.80  thf(cc2_relset_1, axiom,
% 0.57/0.80    (![A:$i,B:$i,C:$i]:
% 0.57/0.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.80       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.57/0.80  thf('56', plain,
% 0.57/0.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.57/0.80         ((v4_relat_1 @ X18 @ X19)
% 0.57/0.80          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.57/0.80      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.57/0.80  thf('57', plain,
% 0.57/0.80      (![X1 : $i, X2 : $i]: (~ (v1_xboole_0 @ X2) | (v4_relat_1 @ X2 @ X1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['55', '56'])).
% 0.57/0.80  thf(d18_relat_1, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( v1_relat_1 @ B ) =>
% 0.57/0.80       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.57/0.80  thf('58', plain,
% 0.57/0.80      (![X16 : $i, X17 : $i]:
% 0.57/0.80         (~ (v4_relat_1 @ X16 @ X17)
% 0.57/0.80          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.57/0.80          | ~ (v1_relat_1 @ X16))),
% 0.57/0.80      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.57/0.80  thf('59', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X1)
% 0.57/0.80          | ~ (v1_relat_1 @ X1)
% 0.57/0.80          | (r1_tarski @ (k1_relat_1 @ X1) @ X0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['57', '58'])).
% 0.57/0.80  thf('60', plain,
% 0.57/0.80      (![X10 : $i, X12 : $i]:
% 0.57/0.80         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.80  thf('61', plain,
% 0.57/0.80      (![X0 : $i, X1 : $i]:
% 0.57/0.80         (~ (v1_relat_1 @ X1)
% 0.57/0.80          | ~ (v1_xboole_0 @ X1)
% 0.57/0.80          | (m1_subset_1 @ (k1_relat_1 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['59', '60'])).
% 0.57/0.80  thf(cc4_relset_1, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( v1_xboole_0 @ A ) =>
% 0.57/0.80       ( ![C:$i]:
% 0.57/0.80         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.57/0.80           ( v1_xboole_0 @ C ) ) ) ))).
% 0.57/0.80  thf('62', plain,
% 0.57/0.80      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X21)
% 0.57/0.80          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 0.57/0.80          | (v1_xboole_0 @ X22))),
% 0.57/0.80      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.57/0.80  thf('63', plain,
% 0.57/0.80      (![X0 : $i, X2 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X2)
% 0.57/0.80          | ~ (v1_relat_1 @ X2)
% 0.57/0.80          | (v1_xboole_0 @ (k1_relat_1 @ X2))
% 0.57/0.80          | ~ (v1_xboole_0 @ X0))),
% 0.57/0.80      inference('sup-', [status(thm)], ['61', '62'])).
% 0.57/0.80  thf('64', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         ((v1_xboole_0 @ sk_A)
% 0.57/0.80          | ~ (v1_xboole_0 @ X0)
% 0.57/0.80          | ~ (v1_relat_1 @ sk_C_1)
% 0.57/0.80          | ~ (v1_xboole_0 @ sk_C_1))),
% 0.57/0.80      inference('sup+', [status(thm)], ['54', '63'])).
% 0.57/0.80  thf('65', plain, ((v1_relat_1 @ sk_C_1)),
% 0.57/0.80      inference('sup-', [status(thm)], ['43', '44'])).
% 0.57/0.80  thf('66', plain,
% 0.57/0.80      (![X0 : $i]:
% 0.57/0.80         ((v1_xboole_0 @ sk_A)
% 0.57/0.80          | ~ (v1_xboole_0 @ X0)
% 0.57/0.80          | ~ (v1_xboole_0 @ sk_C_1))),
% 0.57/0.80      inference('demod', [status(thm)], ['64', '65'])).
% 0.57/0.80  thf('67', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.57/0.80      inference('condensation', [status(thm)], ['66'])).
% 0.57/0.80  thf('68', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.57/0.80      inference('clc', [status(thm)], ['53', '67'])).
% 0.57/0.80  thf('69', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.57/0.80      inference('sup-', [status(thm)], ['38', '39'])).
% 0.57/0.80  thf(t3_funct_2, axiom,
% 0.57/0.80    (![A:$i]:
% 0.57/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.57/0.80       ( ( v1_funct_1 @ A ) & 
% 0.57/0.80         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.57/0.80         ( m1_subset_1 @
% 0.57/0.80           A @ 
% 0.57/0.80           ( k1_zfmisc_1 @
% 0.57/0.80             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.57/0.80  thf('70', plain,
% 0.57/0.80      (![X49 : $i]:
% 0.57/0.80         ((m1_subset_1 @ X49 @ 
% 0.57/0.80           (k1_zfmisc_1 @ 
% 0.57/0.80            (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))))
% 0.57/0.80          | ~ (v1_funct_1 @ X49)
% 0.57/0.80          | ~ (v1_relat_1 @ X49))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.57/0.80  thf('71', plain,
% 0.57/0.80      (((m1_subset_1 @ sk_C_1 @ 
% 0.57/0.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.57/0.80        | ~ (v1_relat_1 @ sk_C_1)
% 0.57/0.80        | ~ (v1_funct_1 @ sk_C_1))),
% 0.57/0.80      inference('sup+', [status(thm)], ['69', '70'])).
% 0.57/0.80  thf('72', plain, ((v1_relat_1 @ sk_C_1)),
% 0.57/0.80      inference('sup-', [status(thm)], ['43', '44'])).
% 0.57/0.80  thf('73', plain, ((v1_funct_1 @ sk_C_1)),
% 0.57/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.80  thf('74', plain,
% 0.57/0.80      ((m1_subset_1 @ sk_C_1 @ 
% 0.57/0.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.57/0.80      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.57/0.80  thf('75', plain,
% 0.57/0.80      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.57/0.80         (~ (v1_xboole_0 @ X21)
% 0.57/0.80          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 0.57/0.80          | (v1_xboole_0 @ X22))),
% 0.57/0.80      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.57/0.80  thf('76', plain,
% 0.57/0.80      (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['74', '75'])).
% 0.57/0.80  thf('77', plain,
% 0.57/0.80      ((m1_subset_1 @ sk_C_1 @ 
% 0.57/0.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.57/0.80      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.57/0.80  thf(cc5_funct_2, axiom,
% 0.57/0.80    (![A:$i,B:$i]:
% 0.57/0.80     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.57/0.80       ( ![C:$i]:
% 0.57/0.80         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.80           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.57/0.80             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.57/0.80  thf('78', plain,
% 0.57/0.80      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.57/0.80         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.57/0.80          | (v1_partfun1 @ X33 @ X34)
% 0.57/0.80          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.57/0.80          | ~ (v1_funct_1 @ X33)
% 0.57/0.80          | (v1_xboole_0 @ X35))),
% 0.57/0.80      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.57/0.80  thf('79', plain,
% 0.57/0.80      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.57/0.80        | ~ (v1_funct_1 @ sk_C_1)
% 0.57/0.80        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.57/0.80        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.57/0.80      inference('sup-', [status(thm)], ['77', '78'])).
% 0.57/0.80  thf('80', plain, ((v1_funct_1 @ sk_C_1)),
% 0.57/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.80  thf('81', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.57/0.80      inference('sup-', [status(thm)], ['38', '39'])).
% 0.57/0.80  thf('82', plain,
% 0.57/0.80      (![X49 : $i]:
% 0.57/0.80         ((v1_funct_2 @ X49 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))
% 0.57/0.80          | ~ (v1_funct_1 @ X49)
% 0.57/0.80          | ~ (v1_relat_1 @ X49))),
% 0.57/0.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.57/0.80  thf('83', plain,
% 0.57/0.80      (((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.57/0.80        | ~ (v1_relat_1 @ sk_C_1)
% 0.57/0.80        | ~ (v1_funct_1 @ sk_C_1))),
% 0.57/0.80      inference('sup+', [status(thm)], ['81', '82'])).
% 0.57/0.80  thf('84', plain, ((v1_relat_1 @ sk_C_1)),
% 0.57/0.80      inference('sup-', [status(thm)], ['43', '44'])).
% 0.57/0.80  thf('85', plain, ((v1_funct_1 @ sk_C_1)),
% 0.57/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.80  thf('86', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 0.57/0.80      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.57/0.80  thf('87', plain,
% 0.57/0.80      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.57/0.80      inference('demod', [status(thm)], ['79', '80', '86'])).
% 0.57/0.80  thf('88', plain,
% 0.57/0.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.57/0.80      inference('sup-', [status(thm)], ['34', '47'])).
% 0.57/0.80  thf('89', plain,
% 0.57/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.57/0.80         (~ (v1_funct_1 @ X27)
% 0.57/0.80          | ~ (v1_partfun1 @ X27 @ X28)
% 0.57/0.80          | (v1_funct_2 @ X27 @ X28 @ X29)
% 0.57/0.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.57/0.80      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.57/0.80  thf('90', plain,
% 0.57/0.80      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.57/0.80        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.57/0.80        | ~ (v1_funct_1 @ sk_C_1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['88', '89'])).
% 0.57/0.80  thf('91', plain, ((v1_funct_1 @ sk_C_1)),
% 0.57/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.80  thf('92', plain,
% 0.57/0.80      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B) | ~ (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.57/0.80      inference('demod', [status(thm)], ['90', '91'])).
% 0.57/0.80  thf('93', plain,
% 0.57/0.80      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.57/0.80         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.57/0.80      inference('split', [status(esa)], ['17'])).
% 0.57/0.80  thf('94', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.57/0.80      inference('sat_resolution*', [status(thm)], ['33', '50', '51'])).
% 0.57/0.80  thf('95', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.57/0.80      inference('simpl_trail', [status(thm)], ['93', '94'])).
% 0.57/0.80  thf('96', plain, (~ (v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.57/0.80      inference('clc', [status(thm)], ['92', '95'])).
% 0.57/0.80  thf('97', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.57/0.80      inference('sup-', [status(thm)], ['87', '96'])).
% 0.57/0.80  thf('98', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.57/0.80      inference('demod', [status(thm)], ['76', '97'])).
% 0.57/0.80  thf('99', plain, ($false), inference('demod', [status(thm)], ['68', '98'])).
% 0.57/0.80  
% 0.57/0.80  % SZS output end Refutation
% 0.57/0.80  
% 0.57/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
