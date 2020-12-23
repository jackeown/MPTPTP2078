%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CX8nNe0lBp

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:52 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  189 (1815 expanded)
%              Number of leaves         :   45 ( 534 expanded)
%              Depth                    :   19
%              Number of atoms          : 1289 (19428 expanded)
%              Number of equality atoms :   53 ( 790 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X52 @ X51 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X52 @ X49 @ X50 ) @ X52 @ X49 @ X50 )
      | ( X51
       != ( k1_funct_2 @ X50 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X49: $i,X50: $i,X52: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X52 @ X49 @ X50 ) @ X52 @ X49 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_funct_2 @ X50 @ X49 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( X44 = X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X44 @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C_1
    = ( sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v1_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X44 @ X43 @ X45 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X42 ) @ X43 )
      | ~ ( zip_tseitin_0 @ X42 @ X44 @ X43 @ X45 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['17'])).

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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relat_1 @ X42 )
        = X45 )
      | ~ ( zip_tseitin_0 @ X42 @ X44 @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('26',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( v1_relat_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X44 @ X43 @ X45 ) ) ),
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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('35',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) @ X23 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('47',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X27: $i] :
      ( ( ( k2_relat_1 @ X27 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X27 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('57',plain,(
    ! [X24: $i] :
      ( ( r1_tarski @ X24 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X24 ) @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('58',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('60',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('68',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','72'])).

thf('74',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('75',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('76',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','80'])).

thf('82',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('83',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('85',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( v1_partfun1 @ X39 @ X40 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('88',plain,
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

thf('89',plain,(
    ! [X55: $i] :
      ( ( v1_funct_2 @ X55 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('90',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('92',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('93',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('96',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_partfun1 @ X33 @ X34 )
      | ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('97',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('99',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('102',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','102'])).

thf('104',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['33','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('106',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','102'])).

thf('107',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_partfun1 @ X33 @ X34 )
      | ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('109',plain,
    ( ( v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_2 )
    | ~ ( v1_partfun1 @ sk_C_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('113',plain,(
    ! [X24: $i] :
      ( ( r1_tarski @ X24 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X24 ) @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('114',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) )
        = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('119',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X32 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('122',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('124',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('130',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['116','117','127','128','129','130'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('132',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X38 ) ) )
      | ( v1_partfun1 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','79'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_partfun1 @ X2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','135'])).

thf('137',plain,
    ( ( v1_partfun1 @ sk_C_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['110','136'])).

thf('138',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('139',plain,(
    v1_partfun1 @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('141',plain,(
    v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_2 ),
    inference(demod,[status(thm)],['109','139','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['104','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CX8nNe0lBp
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.87/1.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.87/1.05  % Solved by: fo/fo7.sh
% 0.87/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.05  % done 1164 iterations in 0.596s
% 0.87/1.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.87/1.05  % SZS output start Refutation
% 0.87/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.87/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.05  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.87/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.87/1.05  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.87/1.05  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.87/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.87/1.05  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.87/1.05  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.87/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.05  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.87/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.87/1.05  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.87/1.05  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.87/1.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.87/1.05  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.87/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.87/1.05  thf(sk_B_type, type, sk_B: $i > $i).
% 0.87/1.05  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.87/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.87/1.05  thf(t121_funct_2, conjecture,
% 0.87/1.05    (![A:$i,B:$i,C:$i]:
% 0.87/1.05     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.87/1.05       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.87/1.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.87/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.05    (~( ![A:$i,B:$i,C:$i]:
% 0.87/1.05        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.87/1.05          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.87/1.05            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.87/1.05    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.87/1.05  thf('0', plain,
% 0.87/1.05      ((~ (v1_funct_1 @ sk_C_1)
% 0.87/1.05        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.87/1.05        | ~ (m1_subset_1 @ sk_C_1 @ 
% 0.87/1.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.87/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.05  thf('1', plain,
% 0.87/1.05      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2))
% 0.87/1.05         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)))),
% 0.87/1.05      inference('split', [status(esa)], ['0'])).
% 0.87/1.05  thf('2', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_2))),
% 0.87/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.05  thf(d2_funct_2, axiom,
% 0.87/1.05    (![A:$i,B:$i,C:$i]:
% 0.87/1.05     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.87/1.05       ( ![D:$i]:
% 0.87/1.05         ( ( r2_hidden @ D @ C ) <=>
% 0.87/1.05           ( ?[E:$i]:
% 0.87/1.05             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.87/1.05               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.87/1.05               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.87/1.05  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.87/1.05  thf(zf_stmt_2, axiom,
% 0.87/1.05    (![E:$i,D:$i,B:$i,A:$i]:
% 0.87/1.05     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.87/1.05       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.87/1.05         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.87/1.05         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.87/1.05  thf(zf_stmt_3, axiom,
% 0.87/1.05    (![A:$i,B:$i,C:$i]:
% 0.87/1.05     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.87/1.05       ( ![D:$i]:
% 0.87/1.05         ( ( r2_hidden @ D @ C ) <=>
% 0.87/1.05           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.87/1.05  thf('3', plain,
% 0.87/1.05      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.87/1.05         (~ (r2_hidden @ X52 @ X51)
% 0.87/1.05          | (zip_tseitin_0 @ (sk_E_1 @ X52 @ X49 @ X50) @ X52 @ X49 @ X50)
% 0.87/1.05          | ((X51) != (k1_funct_2 @ X50 @ X49)))),
% 0.87/1.05      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.87/1.05  thf('4', plain,
% 0.87/1.05      (![X49 : $i, X50 : $i, X52 : $i]:
% 0.87/1.05         ((zip_tseitin_0 @ (sk_E_1 @ X52 @ X49 @ X50) @ X52 @ X49 @ X50)
% 0.87/1.05          | ~ (r2_hidden @ X52 @ (k1_funct_2 @ X50 @ X49)))),
% 0.87/1.05      inference('simplify', [status(thm)], ['3'])).
% 0.87/1.05  thf('5', plain,
% 0.87/1.05      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_C_1 @ sk_B_2 @ 
% 0.87/1.05        sk_A)),
% 0.87/1.05      inference('sup-', [status(thm)], ['2', '4'])).
% 0.87/1.05  thf('6', plain,
% 0.87/1.05      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_C_1 @ sk_B_2 @ 
% 0.87/1.05        sk_A)),
% 0.87/1.05      inference('sup-', [status(thm)], ['2', '4'])).
% 0.87/1.05  thf('7', plain,
% 0.87/1.05      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.05         (((X44) = (X42)) | ~ (zip_tseitin_0 @ X42 @ X44 @ X43 @ X45))),
% 0.87/1.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.87/1.05  thf('8', plain, (((sk_C_1) = (sk_E_1 @ sk_C_1 @ sk_B_2 @ sk_A))),
% 0.87/1.05      inference('sup-', [status(thm)], ['6', '7'])).
% 0.87/1.05  thf('9', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.87/1.05      inference('demod', [status(thm)], ['5', '8'])).
% 0.87/1.05  thf('10', plain,
% 0.87/1.05      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.05         ((v1_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X44 @ X43 @ X45))),
% 0.87/1.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.87/1.05  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 0.87/1.05      inference('sup-', [status(thm)], ['9', '10'])).
% 0.87/1.05  thf('12', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 0.87/1.05      inference('split', [status(esa)], ['0'])).
% 0.87/1.05  thf('13', plain, (((v1_funct_1 @ sk_C_1))),
% 0.87/1.05      inference('sup-', [status(thm)], ['11', '12'])).
% 0.87/1.05  thf('14', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.87/1.05      inference('demod', [status(thm)], ['5', '8'])).
% 0.87/1.05  thf('15', plain,
% 0.87/1.05      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.05         ((r1_tarski @ (k2_relat_1 @ X42) @ X43)
% 0.87/1.05          | ~ (zip_tseitin_0 @ X42 @ X44 @ X43 @ X45))),
% 0.87/1.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.87/1.05  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_2)),
% 0.87/1.05      inference('sup-', [status(thm)], ['14', '15'])).
% 0.87/1.05  thf(d10_xboole_0, axiom,
% 0.87/1.05    (![A:$i,B:$i]:
% 0.87/1.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.87/1.05  thf('17', plain,
% 0.87/1.05      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.87/1.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.05  thf('18', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.87/1.05      inference('simplify', [status(thm)], ['17'])).
% 0.87/1.05  thf(t11_relset_1, axiom,
% 0.87/1.05    (![A:$i,B:$i,C:$i]:
% 0.87/1.05     ( ( v1_relat_1 @ C ) =>
% 0.87/1.05       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.87/1.05           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.87/1.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.87/1.05  thf('19', plain,
% 0.87/1.05      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.87/1.05         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.87/1.05          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ X32)
% 0.87/1.05          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.87/1.05          | ~ (v1_relat_1 @ X30))),
% 0.87/1.05      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.87/1.05  thf('20', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i]:
% 0.87/1.05         (~ (v1_relat_1 @ X0)
% 0.87/1.05          | (m1_subset_1 @ X0 @ 
% 0.87/1.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.87/1.05          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.87/1.05      inference('sup-', [status(thm)], ['18', '19'])).
% 0.87/1.05  thf('21', plain,
% 0.87/1.05      (((m1_subset_1 @ sk_C_1 @ 
% 0.87/1.05         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_2)))
% 0.87/1.05        | ~ (v1_relat_1 @ sk_C_1))),
% 0.87/1.05      inference('sup-', [status(thm)], ['16', '20'])).
% 0.87/1.05  thf('22', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.87/1.05      inference('demod', [status(thm)], ['5', '8'])).
% 0.87/1.05  thf('23', plain,
% 0.87/1.05      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.05         (((k1_relat_1 @ X42) = (X45))
% 0.87/1.05          | ~ (zip_tseitin_0 @ X42 @ X44 @ X43 @ X45))),
% 0.87/1.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.87/1.05  thf('24', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.87/1.05      inference('sup-', [status(thm)], ['22', '23'])).
% 0.87/1.05  thf('25', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.87/1.05      inference('demod', [status(thm)], ['5', '8'])).
% 0.87/1.05  thf('26', plain,
% 0.87/1.05      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.05         ((v1_relat_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X44 @ X43 @ X45))),
% 0.87/1.05      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.87/1.05  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.87/1.05      inference('sup-', [status(thm)], ['25', '26'])).
% 0.87/1.05  thf('28', plain,
% 0.87/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.87/1.05      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.87/1.05  thf('29', plain,
% 0.87/1.05      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))
% 0.87/1.05         <= (~
% 0.87/1.05             ((m1_subset_1 @ sk_C_1 @ 
% 0.87/1.05               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))))),
% 0.87/1.05      inference('split', [status(esa)], ['0'])).
% 0.87/1.05  thf('30', plain,
% 0.87/1.05      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 0.87/1.05      inference('sup-', [status(thm)], ['28', '29'])).
% 0.87/1.05  thf('31', plain,
% 0.87/1.05      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)) | 
% 0.87/1.05       ~
% 0.87/1.05       ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))) | 
% 0.87/1.05       ~ ((v1_funct_1 @ sk_C_1))),
% 0.87/1.05      inference('split', [status(esa)], ['0'])).
% 0.87/1.05  thf('32', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2))),
% 0.87/1.05      inference('sat_resolution*', [status(thm)], ['13', '30', '31'])).
% 0.87/1.05  thf('33', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 0.87/1.05      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.87/1.05  thf(t7_xboole_0, axiom,
% 0.87/1.05    (![A:$i]:
% 0.87/1.05     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.87/1.05          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.87/1.05  thf('34', plain,
% 0.87/1.05      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.87/1.05      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.87/1.05  thf('35', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.87/1.05      inference('simplify', [status(thm)], ['17'])).
% 0.87/1.05  thf(t3_subset, axiom,
% 0.87/1.05    (![A:$i,B:$i]:
% 0.87/1.05     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.87/1.05  thf('36', plain,
% 0.87/1.05      (![X12 : $i, X14 : $i]:
% 0.87/1.05         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.87/1.05      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.05  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['35', '36'])).
% 0.87/1.05  thf(t5_subset, axiom,
% 0.87/1.05    (![A:$i,B:$i,C:$i]:
% 0.87/1.05     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.87/1.05          ( v1_xboole_0 @ C ) ) ))).
% 0.87/1.05  thf('38', plain,
% 0.87/1.05      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.87/1.05         (~ (r2_hidden @ X15 @ X16)
% 0.87/1.05          | ~ (v1_xboole_0 @ X17)
% 0.87/1.05          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.87/1.05      inference('cnf', [status(esa)], [t5_subset])).
% 0.87/1.05  thf('39', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['37', '38'])).
% 0.87/1.05  thf('40', plain,
% 0.87/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['34', '39'])).
% 0.87/1.05  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.87/1.05  thf('41', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.87/1.05      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.05  thf('42', plain,
% 0.87/1.05      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.87/1.05      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.87/1.05  thf(t194_relat_1, axiom,
% 0.87/1.05    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.87/1.05  thf('43', plain,
% 0.87/1.05      (![X22 : $i, X23 : $i]:
% 0.87/1.05         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X22 @ X23)) @ X23)),
% 0.87/1.05      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.87/1.05  thf(d3_tarski, axiom,
% 0.87/1.05    (![A:$i,B:$i]:
% 0.87/1.05     ( ( r1_tarski @ A @ B ) <=>
% 0.87/1.05       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.87/1.05  thf('44', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.05         (~ (r2_hidden @ X0 @ X1)
% 0.87/1.05          | (r2_hidden @ X0 @ X2)
% 0.87/1.05          | ~ (r1_tarski @ X1 @ X2))),
% 0.87/1.05      inference('cnf', [status(esa)], [d3_tarski])).
% 0.87/1.05  thf('45', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.05         ((r2_hidden @ X2 @ X0)
% 0.87/1.05          | ~ (r2_hidden @ X2 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.87/1.05      inference('sup-', [status(thm)], ['43', '44'])).
% 0.87/1.05  thf('46', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i]:
% 0.87/1.05         (((k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) = (k1_xboole_0))
% 0.87/1.05          | (r2_hidden @ (sk_B @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['42', '45'])).
% 0.87/1.05  thf(t7_ordinal1, axiom,
% 0.87/1.05    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.87/1.05  thf('47', plain,
% 0.87/1.05      (![X28 : $i, X29 : $i]:
% 0.87/1.05         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 0.87/1.05      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.87/1.05  thf('48', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i]:
% 0.87/1.05         (((k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) = (k1_xboole_0))
% 0.87/1.05          | ~ (r1_tarski @ X0 @ (sk_B @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))))),
% 0.87/1.05      inference('sup-', [status(thm)], ['46', '47'])).
% 0.87/1.05  thf('49', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['41', '48'])).
% 0.87/1.05  thf(t65_relat_1, axiom,
% 0.87/1.05    (![A:$i]:
% 0.87/1.05     ( ( v1_relat_1 @ A ) =>
% 0.87/1.05       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.87/1.05         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.87/1.05  thf('50', plain,
% 0.87/1.05      (![X27 : $i]:
% 0.87/1.05         (((k2_relat_1 @ X27) != (k1_xboole_0))
% 0.87/1.05          | ((k1_relat_1 @ X27) = (k1_xboole_0))
% 0.87/1.05          | ~ (v1_relat_1 @ X27))),
% 0.87/1.05      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.87/1.05  thf('51', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         (((k1_xboole_0) != (k1_xboole_0))
% 0.87/1.05          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.87/1.05          | ((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.87/1.05      inference('sup-', [status(thm)], ['49', '50'])).
% 0.87/1.05  thf(fc6_relat_1, axiom,
% 0.87/1.05    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.87/1.05  thf('52', plain,
% 0.87/1.05      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.87/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.87/1.05  thf('53', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         (((k1_xboole_0) != (k1_xboole_0))
% 0.87/1.05          | ((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.87/1.05      inference('demod', [status(thm)], ['51', '52'])).
% 0.87/1.05  thf('54', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         ((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.87/1.05      inference('simplify', [status(thm)], ['53'])).
% 0.87/1.05  thf('55', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i]:
% 0.87/1.05         (((k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) = (k1_xboole_0))
% 0.87/1.05          | ~ (v1_xboole_0 @ X0))),
% 0.87/1.05      inference('sup+', [status(thm)], ['40', '54'])).
% 0.87/1.05  thf('56', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.87/1.05      inference('sup-', [status(thm)], ['22', '23'])).
% 0.87/1.05  thf(t21_relat_1, axiom,
% 0.87/1.05    (![A:$i]:
% 0.87/1.05     ( ( v1_relat_1 @ A ) =>
% 0.87/1.05       ( r1_tarski @
% 0.87/1.05         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.87/1.05  thf('57', plain,
% 0.87/1.05      (![X24 : $i]:
% 0.87/1.05         ((r1_tarski @ X24 @ 
% 0.87/1.05           (k2_zfmisc_1 @ (k1_relat_1 @ X24) @ (k2_relat_1 @ X24)))
% 0.87/1.05          | ~ (v1_relat_1 @ X24))),
% 0.87/1.05      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.87/1.05  thf('58', plain,
% 0.87/1.05      (((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))
% 0.87/1.05        | ~ (v1_relat_1 @ sk_C_1))),
% 0.87/1.05      inference('sup+', [status(thm)], ['56', '57'])).
% 0.87/1.05  thf('59', plain, ((v1_relat_1 @ sk_C_1)),
% 0.87/1.05      inference('sup-', [status(thm)], ['25', '26'])).
% 0.87/1.05  thf('60', plain,
% 0.87/1.05      ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 0.87/1.05      inference('demod', [status(thm)], ['58', '59'])).
% 0.87/1.05  thf(t25_relat_1, axiom,
% 0.87/1.05    (![A:$i]:
% 0.87/1.05     ( ( v1_relat_1 @ A ) =>
% 0.87/1.05       ( ![B:$i]:
% 0.87/1.05         ( ( v1_relat_1 @ B ) =>
% 0.87/1.05           ( ( r1_tarski @ A @ B ) =>
% 0.87/1.05             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.87/1.05               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.87/1.05  thf('61', plain,
% 0.87/1.05      (![X25 : $i, X26 : $i]:
% 0.87/1.05         (~ (v1_relat_1 @ X25)
% 0.87/1.05          | (r1_tarski @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25))
% 0.87/1.05          | ~ (r1_tarski @ X26 @ X25)
% 0.87/1.05          | ~ (v1_relat_1 @ X26))),
% 0.87/1.05      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.87/1.05  thf('62', plain,
% 0.87/1.05      ((~ (v1_relat_1 @ sk_C_1)
% 0.87/1.05        | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ 
% 0.87/1.05           (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 0.87/1.05        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.87/1.05      inference('sup-', [status(thm)], ['60', '61'])).
% 0.87/1.05  thf('63', plain, ((v1_relat_1 @ sk_C_1)),
% 0.87/1.05      inference('sup-', [status(thm)], ['25', '26'])).
% 0.87/1.05  thf('64', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.87/1.05      inference('sup-', [status(thm)], ['22', '23'])).
% 0.87/1.05  thf('65', plain,
% 0.87/1.05      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.87/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.87/1.05  thf('66', plain,
% 0.87/1.05      ((r1_tarski @ sk_A @ 
% 0.87/1.05        (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.87/1.05      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.87/1.05  thf('67', plain,
% 0.87/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['34', '39'])).
% 0.87/1.05  thf('68', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.87/1.05      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.05  thf('69', plain,
% 0.87/1.05      (![X5 : $i, X7 : $i]:
% 0.87/1.05         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.87/1.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.05  thf('70', plain,
% 0.87/1.05      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.87/1.05      inference('sup-', [status(thm)], ['68', '69'])).
% 0.87/1.05  thf('71', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i]:
% 0.87/1.05         (~ (r1_tarski @ X1 @ X0)
% 0.87/1.05          | ~ (v1_xboole_0 @ X0)
% 0.87/1.05          | ((X1) = (k1_xboole_0)))),
% 0.87/1.05      inference('sup-', [status(thm)], ['67', '70'])).
% 0.87/1.05  thf('72', plain,
% 0.87/1.05      ((((sk_A) = (k1_xboole_0))
% 0.87/1.05        | ~ (v1_xboole_0 @ 
% 0.87/1.05             (k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))))),
% 0.87/1.05      inference('sup-', [status(thm)], ['66', '71'])).
% 0.87/1.05  thf('73', plain,
% 0.87/1.05      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.87/1.05        | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.87/1.05        | ((sk_A) = (k1_xboole_0)))),
% 0.87/1.05      inference('sup-', [status(thm)], ['55', '72'])).
% 0.87/1.05  thf('74', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.87/1.05      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.05  thf(existence_m1_subset_1, axiom,
% 0.87/1.05    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.87/1.05  thf('75', plain, (![X9 : $i]: (m1_subset_1 @ (sk_B_1 @ X9) @ X9)),
% 0.87/1.05      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.87/1.05  thf(t2_subset, axiom,
% 0.87/1.05    (![A:$i,B:$i]:
% 0.87/1.05     ( ( m1_subset_1 @ A @ B ) =>
% 0.87/1.05       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.87/1.05  thf('76', plain,
% 0.87/1.05      (![X10 : $i, X11 : $i]:
% 0.87/1.05         ((r2_hidden @ X10 @ X11)
% 0.87/1.05          | (v1_xboole_0 @ X11)
% 0.87/1.05          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.87/1.05      inference('cnf', [status(esa)], [t2_subset])).
% 0.87/1.05  thf('77', plain,
% 0.87/1.05      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B_1 @ X0) @ X0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['75', '76'])).
% 0.87/1.05  thf('78', plain,
% 0.87/1.05      (![X28 : $i, X29 : $i]:
% 0.87/1.05         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 0.87/1.05      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.87/1.05  thf('79', plain,
% 0.87/1.05      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B_1 @ X0)))),
% 0.87/1.05      inference('sup-', [status(thm)], ['77', '78'])).
% 0.87/1.05  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.05      inference('sup-', [status(thm)], ['74', '79'])).
% 0.87/1.05  thf('81', plain,
% 0.87/1.05      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | ((sk_A) = (k1_xboole_0)))),
% 0.87/1.05      inference('demod', [status(thm)], ['73', '80'])).
% 0.87/1.05  thf('82', plain,
% 0.87/1.05      ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1)))),
% 0.87/1.05      inference('demod', [status(thm)], ['58', '59'])).
% 0.87/1.05  thf('83', plain,
% 0.87/1.05      (![X12 : $i, X14 : $i]:
% 0.87/1.05         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.87/1.05      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.05  thf('84', plain,
% 0.87/1.05      ((m1_subset_1 @ sk_C_1 @ 
% 0.87/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.87/1.05      inference('sup-', [status(thm)], ['82', '83'])).
% 0.87/1.05  thf(cc5_funct_2, axiom,
% 0.87/1.05    (![A:$i,B:$i]:
% 0.87/1.05     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.87/1.05       ( ![C:$i]:
% 0.87/1.05         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.05           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.87/1.05             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.87/1.05  thf('85', plain,
% 0.87/1.05      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.87/1.05         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.87/1.05          | (v1_partfun1 @ X39 @ X40)
% 0.87/1.05          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.87/1.05          | ~ (v1_funct_1 @ X39)
% 0.87/1.05          | (v1_xboole_0 @ X41))),
% 0.87/1.05      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.87/1.05  thf('86', plain,
% 0.87/1.05      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.87/1.05        | ~ (v1_funct_1 @ sk_C_1)
% 0.87/1.05        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.87/1.05        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.87/1.05      inference('sup-', [status(thm)], ['84', '85'])).
% 0.87/1.05  thf('87', plain, ((v1_funct_1 @ sk_C_1)),
% 0.87/1.05      inference('sup-', [status(thm)], ['9', '10'])).
% 0.87/1.05  thf('88', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.87/1.05      inference('sup-', [status(thm)], ['22', '23'])).
% 0.87/1.05  thf(t3_funct_2, axiom,
% 0.87/1.05    (![A:$i]:
% 0.87/1.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.87/1.05       ( ( v1_funct_1 @ A ) & 
% 0.87/1.05         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.87/1.05         ( m1_subset_1 @
% 0.87/1.05           A @ 
% 0.87/1.05           ( k1_zfmisc_1 @
% 0.87/1.05             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.87/1.05  thf('89', plain,
% 0.87/1.05      (![X55 : $i]:
% 0.87/1.05         ((v1_funct_2 @ X55 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))
% 0.87/1.05          | ~ (v1_funct_1 @ X55)
% 0.87/1.05          | ~ (v1_relat_1 @ X55))),
% 0.87/1.05      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.87/1.05  thf('90', plain,
% 0.87/1.05      (((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 0.87/1.05        | ~ (v1_relat_1 @ sk_C_1)
% 0.87/1.05        | ~ (v1_funct_1 @ sk_C_1))),
% 0.87/1.05      inference('sup+', [status(thm)], ['88', '89'])).
% 0.87/1.05  thf('91', plain, ((v1_relat_1 @ sk_C_1)),
% 0.87/1.05      inference('sup-', [status(thm)], ['25', '26'])).
% 0.87/1.05  thf('92', plain, ((v1_funct_1 @ sk_C_1)),
% 0.87/1.05      inference('sup-', [status(thm)], ['9', '10'])).
% 0.87/1.05  thf('93', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 0.87/1.05      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.87/1.05  thf('94', plain,
% 0.87/1.05      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.87/1.05      inference('demod', [status(thm)], ['86', '87', '93'])).
% 0.87/1.05  thf('95', plain,
% 0.87/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.87/1.05      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.87/1.05  thf(cc1_funct_2, axiom,
% 0.87/1.05    (![A:$i,B:$i,C:$i]:
% 0.87/1.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.05       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.87/1.05         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.87/1.05  thf('96', plain,
% 0.87/1.05      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.87/1.05         (~ (v1_funct_1 @ X33)
% 0.87/1.05          | ~ (v1_partfun1 @ X33 @ X34)
% 0.87/1.05          | (v1_funct_2 @ X33 @ X34 @ X35)
% 0.87/1.05          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.87/1.05      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.87/1.05  thf('97', plain,
% 0.87/1.05      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.87/1.05        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.87/1.05        | ~ (v1_funct_1 @ sk_C_1))),
% 0.87/1.05      inference('sup-', [status(thm)], ['95', '96'])).
% 0.87/1.05  thf('98', plain, ((v1_funct_1 @ sk_C_1)),
% 0.87/1.05      inference('sup-', [status(thm)], ['9', '10'])).
% 0.87/1.05  thf('99', plain,
% 0.87/1.05      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2) | ~ (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.87/1.05      inference('demod', [status(thm)], ['97', '98'])).
% 0.87/1.05  thf('100', plain,
% 0.87/1.05      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.87/1.05        | (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2))),
% 0.87/1.05      inference('sup-', [status(thm)], ['94', '99'])).
% 0.87/1.05  thf('101', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 0.87/1.05      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.87/1.05  thf('102', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.87/1.05      inference('clc', [status(thm)], ['100', '101'])).
% 0.87/1.05  thf('103', plain, (((sk_A) = (k1_xboole_0))),
% 0.87/1.05      inference('demod', [status(thm)], ['81', '102'])).
% 0.87/1.05  thf('104', plain, (~ (v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_2)),
% 0.87/1.05      inference('demod', [status(thm)], ['33', '103'])).
% 0.87/1.05  thf('105', plain,
% 0.87/1.05      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.87/1.05      inference('demod', [status(thm)], ['21', '24', '27'])).
% 0.87/1.05  thf('106', plain, (((sk_A) = (k1_xboole_0))),
% 0.87/1.05      inference('demod', [status(thm)], ['81', '102'])).
% 0.87/1.05  thf('107', plain,
% 0.87/1.05      ((m1_subset_1 @ sk_C_1 @ 
% 0.87/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2)))),
% 0.87/1.05      inference('demod', [status(thm)], ['105', '106'])).
% 0.87/1.05  thf('108', plain,
% 0.87/1.05      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.87/1.05         (~ (v1_funct_1 @ X33)
% 0.87/1.05          | ~ (v1_partfun1 @ X33 @ X34)
% 0.87/1.05          | (v1_funct_2 @ X33 @ X34 @ X35)
% 0.87/1.05          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.87/1.05      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.87/1.05  thf('109', plain,
% 0.87/1.05      (((v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_2)
% 0.87/1.05        | ~ (v1_partfun1 @ sk_C_1 @ k1_xboole_0)
% 0.87/1.05        | ~ (v1_funct_1 @ sk_C_1))),
% 0.87/1.05      inference('sup-', [status(thm)], ['107', '108'])).
% 0.87/1.05  thf('110', plain,
% 0.87/1.05      ((m1_subset_1 @ sk_C_1 @ 
% 0.87/1.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 0.87/1.05      inference('sup-', [status(thm)], ['82', '83'])).
% 0.87/1.05  thf('111', plain,
% 0.87/1.05      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['34', '39'])).
% 0.87/1.05  thf('112', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         ((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.87/1.05      inference('simplify', [status(thm)], ['53'])).
% 0.87/1.05  thf('113', plain,
% 0.87/1.05      (![X24 : $i]:
% 0.87/1.05         ((r1_tarski @ X24 @ 
% 0.87/1.05           (k2_zfmisc_1 @ (k1_relat_1 @ X24) @ (k2_relat_1 @ X24)))
% 0.87/1.05          | ~ (v1_relat_1 @ X24))),
% 0.87/1.05      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.87/1.05  thf('114', plain,
% 0.87/1.05      (![X5 : $i, X7 : $i]:
% 0.87/1.05         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.87/1.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.05  thf('115', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         (~ (v1_relat_1 @ X0)
% 0.87/1.05          | ~ (r1_tarski @ 
% 0.87/1.05               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 0.87/1.05          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 0.87/1.05      inference('sup-', [status(thm)], ['113', '114'])).
% 0.87/1.05  thf('116', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         (~ (r1_tarski @ 
% 0.87/1.05             (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.87/1.05              (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))) @ 
% 0.87/1.05             (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.87/1.05          | ((k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) @ 
% 0.87/1.05              (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))
% 0.87/1.05              = (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.87/1.05          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 0.87/1.05      inference('sup-', [status(thm)], ['112', '115'])).
% 0.87/1.05  thf('117', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['41', '48'])).
% 0.87/1.05  thf('118', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         ((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.87/1.05      inference('simplify', [status(thm)], ['53'])).
% 0.87/1.05  thf('119', plain,
% 0.87/1.05      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.87/1.05         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.87/1.05          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ X32)
% 0.87/1.05          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.87/1.05          | ~ (v1_relat_1 @ X30))),
% 0.87/1.05      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.87/1.05  thf('120', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.05         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.87/1.05          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ k1_xboole_0))
% 0.87/1.05          | (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ k1_xboole_0) @ 
% 0.87/1.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.87/1.05          | ~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ k1_xboole_0)) @ X2))),
% 0.87/1.05      inference('sup-', [status(thm)], ['118', '119'])).
% 0.87/1.05  thf('121', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.87/1.05      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.05  thf('122', plain,
% 0.87/1.05      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.87/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.87/1.05  thf('123', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['41', '48'])).
% 0.87/1.05  thf('124', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.87/1.05      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.05  thf('125', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.05         (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ k1_xboole_0) @ 
% 0.87/1.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))),
% 0.87/1.05      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 0.87/1.05  thf('126', plain,
% 0.87/1.05      (![X12 : $i, X13 : $i]:
% 0.87/1.05         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.87/1.05      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.05  thf('127', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.05         (r1_tarski @ (k2_zfmisc_1 @ X2 @ k1_xboole_0) @ 
% 0.87/1.05          (k2_zfmisc_1 @ X1 @ X0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['125', '126'])).
% 0.87/1.05  thf('128', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         ((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.87/1.05      inference('simplify', [status(thm)], ['53'])).
% 0.87/1.05  thf('129', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['41', '48'])).
% 0.87/1.05  thf('130', plain,
% 0.87/1.05      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.87/1.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.87/1.05  thf('131', plain,
% 0.87/1.05      (![X0 : $i]:
% 0.87/1.05         ((k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.87/1.05           = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.87/1.05      inference('demod', [status(thm)],
% 0.87/1.05                ['116', '117', '127', '128', '129', '130'])).
% 0.87/1.05  thf(cc1_partfun1, axiom,
% 0.87/1.05    (![A:$i,B:$i]:
% 0.87/1.05     ( ( v1_xboole_0 @ A ) =>
% 0.87/1.05       ( ![C:$i]:
% 0.87/1.05         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.05           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.87/1.05  thf('132', plain,
% 0.87/1.05      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.87/1.05         (~ (v1_xboole_0 @ X36)
% 0.87/1.05          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X38)))
% 0.87/1.05          | (v1_partfun1 @ X37 @ X36))),
% 0.87/1.05      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.87/1.05  thf('133', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i]:
% 0.87/1.05         (~ (m1_subset_1 @ X1 @ 
% 0.87/1.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))
% 0.87/1.05          | (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.87/1.05          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['131', '132'])).
% 0.87/1.05  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.05      inference('sup-', [status(thm)], ['74', '79'])).
% 0.87/1.05  thf('135', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i]:
% 0.87/1.05         (~ (m1_subset_1 @ X1 @ 
% 0.87/1.05             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))
% 0.87/1.05          | (v1_partfun1 @ X1 @ k1_xboole_0))),
% 0.87/1.05      inference('demod', [status(thm)], ['133', '134'])).
% 0.87/1.05  thf('136', plain,
% 0.87/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.05         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.87/1.05          | ~ (v1_xboole_0 @ X0)
% 0.87/1.05          | (v1_partfun1 @ X2 @ k1_xboole_0))),
% 0.87/1.05      inference('sup-', [status(thm)], ['111', '135'])).
% 0.87/1.05  thf('137', plain,
% 0.87/1.05      (((v1_partfun1 @ sk_C_1 @ k1_xboole_0)
% 0.87/1.05        | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)))),
% 0.87/1.05      inference('sup-', [status(thm)], ['110', '136'])).
% 0.87/1.05  thf('138', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.87/1.05      inference('clc', [status(thm)], ['100', '101'])).
% 0.87/1.05  thf('139', plain, ((v1_partfun1 @ sk_C_1 @ k1_xboole_0)),
% 0.87/1.05      inference('demod', [status(thm)], ['137', '138'])).
% 0.87/1.05  thf('140', plain, ((v1_funct_1 @ sk_C_1)),
% 0.87/1.05      inference('sup-', [status(thm)], ['9', '10'])).
% 0.87/1.05  thf('141', plain, ((v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ sk_B_2)),
% 0.87/1.05      inference('demod', [status(thm)], ['109', '139', '140'])).
% 0.87/1.05  thf('142', plain, ($false), inference('demod', [status(thm)], ['104', '141'])).
% 0.87/1.05  
% 0.87/1.05  % SZS output end Refutation
% 0.87/1.05  
% 0.87/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
