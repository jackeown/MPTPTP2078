%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xi803xlM4K

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:53 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 756 expanded)
%              Number of leaves         :   35 ( 224 expanded)
%              Depth                    :   18
%              Number of atoms          :  824 (8542 expanded)
%              Number of equality atoms :   23 ( 325 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ( ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 )
   <= ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_C_2 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X42 @ X41 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X42 @ X39 @ X40 ) @ X42 @ X39 @ X40 )
      | ( X41
       != ( k1_funct_2 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X39: $i,X40: $i,X42: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X42 @ X39 @ X40 ) @ X42 @ X39 @ X40 )
      | ~ ( r2_hidden @ X42 @ ( k1_funct_2 @ X40 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_2 @ sk_B_1 @ sk_A ) @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_2 @ sk_B_1 @ sk_A ) @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X34 = X32 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C_2
    = ( sk_E_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_funct_1 @ X32 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
   <= ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X33 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('20',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relat_1 @ X32 )
        = X35 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('25',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( zip_tseitin_0 @ X32 @ X34 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf('30',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['13','31','32'])).

thf('34',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_partfun1 @ X23 @ X24 )
      | ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C_2 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('39',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X45: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X28 ) ) )
      | ( v1_partfun1 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('46',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('50',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ ( sk_D_1 @ X10 @ X8 ) ) @ X8 )
      | ( X9
       != ( k1_relat_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('52',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ ( sk_D_1 @ X10 @ X8 ) ) @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ( X16
       != ( k2_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k2_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_C_2 ) @ ( k2_relat_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('59',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) @ sk_C_2 ) @ ( k2_relat_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('63',plain,(
    ! [X45: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('68',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( v1_partfun1 @ X29 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('72',plain,(
    ! [X45: $i] :
      ( ( v1_funct_2 @ X45 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('73',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('75',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('76',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','76'])).

thf('78',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('81',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['61','81'])).

thf('83',plain,(
    v1_partfun1 @ sk_C_2 @ sk_A ),
    inference(demod,[status(thm)],['48','82'])).

thf('84',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['39','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['34','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xi803xlM4K
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.71  % Solved by: fo/fo7.sh
% 0.51/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.71  % done 304 iterations in 0.243s
% 0.51/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.71  % SZS output start Refutation
% 0.51/0.71  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.51/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.51/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.71  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.51/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.71  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.51/0.71  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.51/0.71  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.51/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.51/0.71  thf(t121_funct_2, conjecture,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.51/0.71       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.51/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.71        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.51/0.71          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.71            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.51/0.71    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.51/0.71  thf('0', plain,
% 0.51/0.71      ((~ (v1_funct_1 @ sk_C_2)
% 0.51/0.71        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)
% 0.51/0.71        | ~ (m1_subset_1 @ sk_C_2 @ 
% 0.51/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('1', plain,
% 0.51/0.71      ((~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1))
% 0.51/0.71         <= (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.51/0.71      inference('split', [status(esa)], ['0'])).
% 0.51/0.71  thf('2', plain, ((r2_hidden @ sk_C_2 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf(d2_funct_2, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.51/0.71       ( ![D:$i]:
% 0.51/0.71         ( ( r2_hidden @ D @ C ) <=>
% 0.51/0.71           ( ?[E:$i]:
% 0.51/0.71             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.51/0.71               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.51/0.71               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.51/0.71  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.51/0.71  thf(zf_stmt_2, axiom,
% 0.51/0.71    (![E:$i,D:$i,B:$i,A:$i]:
% 0.51/0.71     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.51/0.71       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.51/0.71         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.51/0.71         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.51/0.71  thf(zf_stmt_3, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.51/0.71       ( ![D:$i]:
% 0.51/0.71         ( ( r2_hidden @ D @ C ) <=>
% 0.51/0.71           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.51/0.71  thf('3', plain,
% 0.51/0.71      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X42 @ X41)
% 0.51/0.71          | (zip_tseitin_0 @ (sk_E_1 @ X42 @ X39 @ X40) @ X42 @ X39 @ X40)
% 0.51/0.71          | ((X41) != (k1_funct_2 @ X40 @ X39)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.51/0.71  thf('4', plain,
% 0.51/0.71      (![X39 : $i, X40 : $i, X42 : $i]:
% 0.51/0.71         ((zip_tseitin_0 @ (sk_E_1 @ X42 @ X39 @ X40) @ X42 @ X39 @ X40)
% 0.51/0.71          | ~ (r2_hidden @ X42 @ (k1_funct_2 @ X40 @ X39)))),
% 0.51/0.71      inference('simplify', [status(thm)], ['3'])).
% 0.51/0.71  thf('5', plain,
% 0.51/0.71      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_2 @ sk_B_1 @ sk_A) @ sk_C_2 @ sk_B_1 @ 
% 0.51/0.71        sk_A)),
% 0.51/0.71      inference('sup-', [status(thm)], ['2', '4'])).
% 0.51/0.71  thf('6', plain,
% 0.51/0.71      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_2 @ sk_B_1 @ sk_A) @ sk_C_2 @ sk_B_1 @ 
% 0.51/0.71        sk_A)),
% 0.51/0.71      inference('sup-', [status(thm)], ['2', '4'])).
% 0.51/0.71  thf('7', plain,
% 0.51/0.71      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.51/0.71         (((X34) = (X32)) | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.71  thf('8', plain, (((sk_C_2) = (sk_E_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.51/0.71  thf('9', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 0.51/0.71      inference('demod', [status(thm)], ['5', '8'])).
% 0.51/0.71  thf('10', plain,
% 0.51/0.71      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.51/0.71         ((v1_funct_1 @ X32) | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.71  thf('11', plain, ((v1_funct_1 @ sk_C_2)),
% 0.51/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('12', plain, ((~ (v1_funct_1 @ sk_C_2)) <= (~ ((v1_funct_1 @ sk_C_2)))),
% 0.51/0.71      inference('split', [status(esa)], ['0'])).
% 0.51/0.71  thf('13', plain, (((v1_funct_1 @ sk_C_2))),
% 0.51/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.51/0.71  thf(d10_xboole_0, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.71  thf('14', plain,
% 0.51/0.71      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.51/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.71  thf('15', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.51/0.71      inference('simplify', [status(thm)], ['14'])).
% 0.51/0.71  thf('16', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 0.51/0.71      inference('demod', [status(thm)], ['5', '8'])).
% 0.51/0.71  thf('17', plain,
% 0.51/0.71      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.51/0.71         ((r1_tarski @ (k2_relat_1 @ X32) @ X33)
% 0.51/0.71          | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.71  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.51/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.71  thf('19', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 0.51/0.71      inference('demod', [status(thm)], ['5', '8'])).
% 0.51/0.71  thf('20', plain,
% 0.51/0.71      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.51/0.71         (((k1_relat_1 @ X32) = (X35))
% 0.51/0.71          | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.71  thf('21', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.71  thf(t11_relset_1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( v1_relat_1 @ C ) =>
% 0.51/0.71       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.51/0.71           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.51/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.51/0.71  thf('22', plain,
% 0.51/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.71         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.51/0.71          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.51/0.71          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.51/0.71          | ~ (v1_relat_1 @ X20))),
% 0.51/0.71      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.51/0.71  thf('23', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         (~ (r1_tarski @ sk_A @ X0)
% 0.51/0.71          | ~ (v1_relat_1 @ sk_C_2)
% 0.51/0.71          | (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.51/0.71          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.51/0.71  thf('24', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 0.51/0.71      inference('demod', [status(thm)], ['5', '8'])).
% 0.51/0.71  thf('25', plain,
% 0.51/0.71      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.51/0.71         ((v1_relat_1 @ X32) | ~ (zip_tseitin_0 @ X32 @ X34 @ X33 @ X35))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.71  thf('26', plain, ((v1_relat_1 @ sk_C_2)),
% 0.51/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.71  thf('27', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         (~ (r1_tarski @ sk_A @ X0)
% 0.51/0.71          | (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.51/0.71          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X1))),
% 0.51/0.71      inference('demod', [status(thm)], ['23', '26'])).
% 0.51/0.71  thf('28', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.51/0.71          | ~ (r1_tarski @ sk_A @ X0))),
% 0.51/0.71      inference('sup-', [status(thm)], ['18', '27'])).
% 0.51/0.71  thf('29', plain,
% 0.51/0.71      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['15', '28'])).
% 0.51/0.71  thf('30', plain,
% 0.51/0.71      ((~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.51/0.71         <= (~
% 0.51/0.71             ((m1_subset_1 @ sk_C_2 @ 
% 0.51/0.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))),
% 0.51/0.71      inference('split', [status(esa)], ['0'])).
% 0.51/0.71  thf('31', plain,
% 0.51/0.71      (((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 0.51/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.51/0.71  thf('32', plain,
% 0.51/0.71      (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)) | 
% 0.51/0.71       ~
% 0.51/0.71       ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))) | 
% 0.51/0.71       ~ ((v1_funct_1 @ sk_C_2))),
% 0.51/0.71      inference('split', [status(esa)], ['0'])).
% 0.51/0.71  thf('33', plain, (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1))),
% 0.51/0.71      inference('sat_resolution*', [status(thm)], ['13', '31', '32'])).
% 0.51/0.71  thf('34', plain, (~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.51/0.71      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.51/0.71  thf('35', plain,
% 0.51/0.71      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['15', '28'])).
% 0.51/0.71  thf(cc1_funct_2, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.71       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.51/0.71         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.51/0.71  thf('36', plain,
% 0.51/0.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.51/0.71         (~ (v1_funct_1 @ X23)
% 0.51/0.71          | ~ (v1_partfun1 @ X23 @ X24)
% 0.51/0.71          | (v1_funct_2 @ X23 @ X24 @ X25)
% 0.51/0.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.51/0.71      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.51/0.71  thf('37', plain,
% 0.51/0.71      (((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)
% 0.51/0.71        | ~ (v1_partfun1 @ sk_C_2 @ sk_A)
% 0.51/0.71        | ~ (v1_funct_1 @ sk_C_2))),
% 0.51/0.71      inference('sup-', [status(thm)], ['35', '36'])).
% 0.51/0.71  thf('38', plain, ((v1_funct_1 @ sk_C_2)),
% 0.51/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('39', plain,
% 0.51/0.71      (((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1) | ~ (v1_partfun1 @ sk_C_2 @ sk_A))),
% 0.51/0.71      inference('demod', [status(thm)], ['37', '38'])).
% 0.51/0.71  thf('40', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.71  thf(t3_funct_2, axiom,
% 0.51/0.71    (![A:$i]:
% 0.51/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.71       ( ( v1_funct_1 @ A ) & 
% 0.51/0.71         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.51/0.71         ( m1_subset_1 @
% 0.51/0.71           A @ 
% 0.51/0.71           ( k1_zfmisc_1 @
% 0.51/0.71             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.51/0.71  thf('41', plain,
% 0.51/0.71      (![X45 : $i]:
% 0.51/0.71         ((m1_subset_1 @ X45 @ 
% 0.51/0.71           (k1_zfmisc_1 @ 
% 0.51/0.71            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))))
% 0.51/0.71          | ~ (v1_funct_1 @ X45)
% 0.51/0.71          | ~ (v1_relat_1 @ X45))),
% 0.51/0.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.51/0.71  thf(cc1_partfun1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( v1_xboole_0 @ A ) =>
% 0.51/0.71       ( ![C:$i]:
% 0.51/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.71           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.51/0.71  thf('42', plain,
% 0.51/0.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.51/0.71         (~ (v1_xboole_0 @ X26)
% 0.51/0.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X28)))
% 0.51/0.71          | (v1_partfun1 @ X27 @ X26))),
% 0.51/0.71      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.51/0.71  thf('43', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         (~ (v1_relat_1 @ X0)
% 0.51/0.71          | ~ (v1_funct_1 @ X0)
% 0.51/0.71          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.51/0.71          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.51/0.71  thf('44', plain,
% 0.51/0.71      ((~ (v1_xboole_0 @ sk_A)
% 0.51/0.71        | (v1_partfun1 @ sk_C_2 @ (k1_relat_1 @ sk_C_2))
% 0.51/0.71        | ~ (v1_funct_1 @ sk_C_2)
% 0.51/0.71        | ~ (v1_relat_1 @ sk_C_2))),
% 0.51/0.71      inference('sup-', [status(thm)], ['40', '43'])).
% 0.51/0.71  thf('45', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.71  thf('46', plain, ((v1_funct_1 @ sk_C_2)),
% 0.51/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('47', plain, ((v1_relat_1 @ sk_C_2)),
% 0.51/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.71  thf('48', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 0.51/0.71      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.51/0.71  thf('49', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.71  thf(d1_xboole_0, axiom,
% 0.51/0.71    (![A:$i]:
% 0.51/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.71  thf('50', plain,
% 0.51/0.71      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.71  thf(d4_relat_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.51/0.71       ( ![C:$i]:
% 0.51/0.71         ( ( r2_hidden @ C @ B ) <=>
% 0.51/0.71           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.51/0.71  thf('51', plain,
% 0.51/0.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.51/0.71         (~ (r2_hidden @ X10 @ X9)
% 0.51/0.71          | (r2_hidden @ (k4_tarski @ X10 @ (sk_D_1 @ X10 @ X8)) @ X8)
% 0.51/0.71          | ((X9) != (k1_relat_1 @ X8)))),
% 0.51/0.71      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.51/0.71  thf('52', plain,
% 0.51/0.71      (![X8 : $i, X10 : $i]:
% 0.51/0.71         ((r2_hidden @ (k4_tarski @ X10 @ (sk_D_1 @ X10 @ X8)) @ X8)
% 0.51/0.71          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X8)))),
% 0.51/0.71      inference('simplify', [status(thm)], ['51'])).
% 0.51/0.71  thf('53', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.51/0.71          | (r2_hidden @ 
% 0.51/0.71             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.51/0.71              (sk_D_1 @ (sk_B @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.51/0.71             X0))),
% 0.51/0.71      inference('sup-', [status(thm)], ['50', '52'])).
% 0.51/0.71  thf(d5_relat_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.51/0.71       ( ![C:$i]:
% 0.51/0.71         ( ( r2_hidden @ C @ B ) <=>
% 0.51/0.71           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.51/0.71  thf('54', plain,
% 0.51/0.71      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.51/0.71         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 0.51/0.71          | (r2_hidden @ X14 @ X16)
% 0.51/0.71          | ((X16) != (k2_relat_1 @ X15)))),
% 0.51/0.71      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.51/0.71  thf('55', plain,
% 0.51/0.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.51/0.71         ((r2_hidden @ X14 @ (k2_relat_1 @ X15))
% 0.51/0.71          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15))),
% 0.51/0.71      inference('simplify', [status(thm)], ['54'])).
% 0.51/0.71  thf('56', plain,
% 0.51/0.71      (![X0 : $i]:
% 0.51/0.71         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.51/0.71          | (r2_hidden @ (sk_D_1 @ (sk_B @ (k1_relat_1 @ X0)) @ X0) @ 
% 0.51/0.71             (k2_relat_1 @ X0)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['53', '55'])).
% 0.51/0.71  thf('57', plain,
% 0.51/0.71      (((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_C_2) @ (k2_relat_1 @ sk_C_2))
% 0.51/0.71        | (v1_xboole_0 @ (k1_relat_1 @ sk_C_2)))),
% 0.51/0.71      inference('sup+', [status(thm)], ['49', '56'])).
% 0.51/0.71  thf('58', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.71  thf('59', plain,
% 0.51/0.71      (((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A) @ sk_C_2) @ (k2_relat_1 @ sk_C_2))
% 0.51/0.71        | (v1_xboole_0 @ sk_A))),
% 0.51/0.71      inference('demod', [status(thm)], ['57', '58'])).
% 0.51/0.71  thf('60', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.71  thf('61', plain,
% 0.51/0.71      (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_2)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['59', '60'])).
% 0.51/0.71  thf('62', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.71  thf('63', plain,
% 0.51/0.71      (![X45 : $i]:
% 0.51/0.71         ((m1_subset_1 @ X45 @ 
% 0.51/0.71           (k1_zfmisc_1 @ 
% 0.51/0.71            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))))
% 0.51/0.71          | ~ (v1_funct_1 @ X45)
% 0.51/0.71          | ~ (v1_relat_1 @ X45))),
% 0.51/0.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.51/0.71  thf('64', plain,
% 0.51/0.71      (((m1_subset_1 @ sk_C_2 @ 
% 0.51/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2))))
% 0.51/0.71        | ~ (v1_relat_1 @ sk_C_2)
% 0.51/0.71        | ~ (v1_funct_1 @ sk_C_2))),
% 0.51/0.71      inference('sup+', [status(thm)], ['62', '63'])).
% 0.51/0.71  thf('65', plain, ((v1_relat_1 @ sk_C_2)),
% 0.51/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.71  thf('66', plain, ((v1_funct_1 @ sk_C_2)),
% 0.51/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('67', plain,
% 0.51/0.71      ((m1_subset_1 @ sk_C_2 @ 
% 0.51/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_2))))),
% 0.51/0.71      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.51/0.71  thf(cc5_funct_2, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.51/0.71       ( ![C:$i]:
% 0.51/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.71           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.51/0.71             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.51/0.71  thf('68', plain,
% 0.51/0.71      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.51/0.71         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.51/0.71          | (v1_partfun1 @ X29 @ X30)
% 0.51/0.71          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.51/0.71          | ~ (v1_funct_1 @ X29)
% 0.51/0.71          | (v1_xboole_0 @ X31))),
% 0.51/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.51/0.71  thf('69', plain,
% 0.51/0.71      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))
% 0.51/0.71        | ~ (v1_funct_1 @ sk_C_2)
% 0.51/0.71        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ (k2_relat_1 @ sk_C_2))
% 0.51/0.71        | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['67', '68'])).
% 0.51/0.71  thf('70', plain, ((v1_funct_1 @ sk_C_2)),
% 0.51/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('71', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.51/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.71  thf('72', plain,
% 0.51/0.71      (![X45 : $i]:
% 0.51/0.71         ((v1_funct_2 @ X45 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))
% 0.51/0.71          | ~ (v1_funct_1 @ X45)
% 0.51/0.71          | ~ (v1_relat_1 @ X45))),
% 0.51/0.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.51/0.71  thf('73', plain,
% 0.51/0.71      (((v1_funct_2 @ sk_C_2 @ sk_A @ (k2_relat_1 @ sk_C_2))
% 0.51/0.71        | ~ (v1_relat_1 @ sk_C_2)
% 0.51/0.71        | ~ (v1_funct_1 @ sk_C_2))),
% 0.51/0.71      inference('sup+', [status(thm)], ['71', '72'])).
% 0.51/0.71  thf('74', plain, ((v1_relat_1 @ sk_C_2)),
% 0.51/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.71  thf('75', plain, ((v1_funct_1 @ sk_C_2)),
% 0.51/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf('76', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ (k2_relat_1 @ sk_C_2))),
% 0.51/0.71      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.51/0.71  thf('77', plain,
% 0.51/0.71      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2)) | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 0.51/0.71      inference('demod', [status(thm)], ['69', '70', '76'])).
% 0.51/0.71  thf('78', plain,
% 0.51/0.71      (((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1) | ~ (v1_partfun1 @ sk_C_2 @ sk_A))),
% 0.51/0.71      inference('demod', [status(thm)], ['37', '38'])).
% 0.51/0.71  thf('79', plain,
% 0.51/0.71      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))
% 0.51/0.71        | (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1))),
% 0.51/0.71      inference('sup-', [status(thm)], ['77', '78'])).
% 0.51/0.71  thf('80', plain, (~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.51/0.71      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.51/0.71  thf('81', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))),
% 0.51/0.71      inference('clc', [status(thm)], ['79', '80'])).
% 0.51/0.71  thf('82', plain, ((v1_xboole_0 @ sk_A)),
% 0.51/0.71      inference('demod', [status(thm)], ['61', '81'])).
% 0.51/0.71  thf('83', plain, ((v1_partfun1 @ sk_C_2 @ sk_A)),
% 0.51/0.71      inference('demod', [status(thm)], ['48', '82'])).
% 0.51/0.71  thf('84', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.51/0.71      inference('demod', [status(thm)], ['39', '83'])).
% 0.51/0.71  thf('85', plain, ($false), inference('demod', [status(thm)], ['34', '84'])).
% 0.51/0.71  
% 0.51/0.71  % SZS output end Refutation
% 0.51/0.71  
% 0.51/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
