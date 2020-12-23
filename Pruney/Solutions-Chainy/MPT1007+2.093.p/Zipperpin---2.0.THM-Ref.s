%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8DnCa7cm8x

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:28 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 130 expanded)
%              Number of leaves         :   44 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  730 (1212 expanded)
%              Number of equality atoms :   51 (  74 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('1',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
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

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
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

thf('6',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_mcart_1 @ X30 )
        = X29 )
      | ~ ( r2_hidden @ X30 @ ( k2_zfmisc_1 @ ( k1_tarski @ X29 ) @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('18',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('21',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_1 @ sk_C ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('25',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X46 @ X43 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','34'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('37',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X23 )
       != X21 )
      | ~ ( r2_hidden @ X24 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X24 @ ( sk_E @ X24 @ X23 ) ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','40'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('46',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('51',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( sk_B @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['49','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8DnCa7cm8x
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 461 iterations in 0.294s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.54/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.54/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.75  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.75  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.54/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.75  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.54/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.75  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.54/0.75  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.54/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.75  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.54/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.75  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.54/0.75  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.75  thf(t9_mcart_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.54/0.75          ( ![B:$i]:
% 0.54/0.75            ( ~( ( r2_hidden @ B @ A ) & 
% 0.54/0.75                 ( ![C:$i,D:$i]:
% 0.54/0.75                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.54/0.75                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.75  thf('0', plain,
% 0.54/0.75      (![X32 : $i]:
% 0.54/0.75         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X32) @ X32))),
% 0.54/0.75      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.54/0.75  thf(t61_funct_2, conjecture,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.54/0.75         ( m1_subset_1 @
% 0.54/0.75           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.54/0.75       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.54/0.75         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.75        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.54/0.75            ( m1_subset_1 @
% 0.54/0.75              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.54/0.75          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.54/0.75            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.54/0.75  thf('1', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(d1_funct_2, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.75           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.54/0.75             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.54/0.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.75           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.54/0.75             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_1, axiom,
% 0.54/0.75    (![C:$i,B:$i,A:$i]:
% 0.54/0.75     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.54/0.75       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.54/0.75         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.54/0.75          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.54/0.75          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      ((~ (zip_tseitin_1 @ sk_C @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.54/0.75        | ((k1_tarski @ sk_A)
% 0.54/0.75            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.75  thf(zf_stmt_2, axiom,
% 0.54/0.75    (![B:$i,A:$i]:
% 0.54/0.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.75       ( zip_tseitin_0 @ B @ A ) ))).
% 0.54/0.75  thf('4', plain,
% 0.54/0.75      (![X35 : $i, X36 : $i]:
% 0.54/0.75         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.54/0.75  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.54/0.75  thf(zf_stmt_5, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.54/0.75         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.75           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.75             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.54/0.75         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.54/0.75          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.54/0.75          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.75  thf('7', plain,
% 0.54/0.75      (((zip_tseitin_1 @ sk_C @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.54/0.75        | ~ (zip_tseitin_0 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      ((((sk_B_2) = (k1_xboole_0))
% 0.54/0.75        | (zip_tseitin_1 @ sk_C @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['4', '7'])).
% 0.54/0.75  thf('9', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('10', plain, ((zip_tseitin_1 @ sk_C @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['3', '10'])).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X32 : $i]:
% 0.54/0.75         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X32) @ X32))),
% 0.54/0.75      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(l3_subset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.54/0.75  thf('14', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X10 @ X11)
% 0.54/0.75          | (r2_hidden @ X10 @ X12)
% 0.54/0.75          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.54/0.75      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.54/0.75  thf('15', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.54/0.75          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      ((((sk_C) = (k1_xboole_0))
% 0.54/0.75        | (r2_hidden @ (sk_B_1 @ sk_C) @ 
% 0.54/0.75           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['12', '15'])).
% 0.54/0.75  thf(t12_mcart_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.54/0.75       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.54/0.75         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.54/0.75         (((k1_mcart_1 @ X30) = (X29))
% 0.54/0.75          | ~ (r2_hidden @ X30 @ (k2_zfmisc_1 @ (k1_tarski @ X29) @ X31)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      ((((sk_C) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B_1 @ sk_C)) = (sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      ((((sk_C) = (k1_xboole_0))
% 0.54/0.75        | (r2_hidden @ (sk_B_1 @ sk_C) @ 
% 0.54/0.75           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['12', '15'])).
% 0.54/0.75  thf(t10_mcart_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.54/0.75       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.54/0.75         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.75         ((r2_hidden @ (k1_mcart_1 @ X26) @ X27)
% 0.54/0.75          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      ((((sk_C) = (k1_xboole_0))
% 0.54/0.75        | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ sk_C)) @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.54/0.75        | ((sk_C) = (k1_xboole_0))
% 0.54/0.75        | ((sk_C) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['18', '21'])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      ((((sk_C) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['22'])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(t7_funct_2, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.75       ( ( r2_hidden @ C @ A ) =>
% 0.54/0.75         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.75           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X43 @ X44)
% 0.54/0.75          | ((X45) = (k1_xboole_0))
% 0.54/0.75          | ~ (v1_funct_1 @ X46)
% 0.54/0.75          | ~ (v1_funct_2 @ X46 @ X44 @ X45)
% 0.54/0.75          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.54/0.75          | (r2_hidden @ (k1_funct_1 @ X46 @ X43) @ X45))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.54/0.75          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.54/0.75          | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75          | ((sk_B_2) = (k1_xboole_0))
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.75  thf('27', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('29', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.54/0.75          | ((sk_B_2) = (k1_xboole_0))
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.54/0.75  thf('30', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      ((((sk_C) = (k1_xboole_0))
% 0.54/0.75        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2))),
% 0.54/0.75      inference('sup-', [status(thm)], ['23', '31'])).
% 0.54/0.75  thf('33', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('34', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.75      inference('clc', [status(thm)], ['32', '33'])).
% 0.54/0.75  thf('35', plain,
% 0.54/0.75      (((k1_tarski @ sk_A)
% 0.54/0.75         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['11', '34'])).
% 0.54/0.75  thf(t4_subset_1, axiom,
% 0.54/0.75    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.54/0.75  thf('36', plain,
% 0.54/0.75      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.54/0.75      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.54/0.75  thf(t22_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.54/0.75       ( ( ![D:$i]:
% 0.54/0.75           ( ~( ( r2_hidden @ D @ B ) & 
% 0.54/0.75                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.54/0.75         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.54/0.75  thf('37', plain,
% 0.54/0.75      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.75         (((k1_relset_1 @ X21 @ X22 @ X23) != (X21))
% 0.54/0.75          | ~ (r2_hidden @ X24 @ X21)
% 0.54/0.75          | (r2_hidden @ (k4_tarski @ X24 @ (sk_E @ X24 @ X23)) @ X23)
% 0.54/0.75          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.54/0.75      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 0.54/0.75           k1_xboole_0)
% 0.54/0.75          | ~ (r2_hidden @ X2 @ X1)
% 0.54/0.75          | ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) != (X1)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['36', '37'])).
% 0.54/0.75  thf('39', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.54/0.75          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.54/0.75             k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['35', '38'])).
% 0.54/0.75  thf('40', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.54/0.75           k1_xboole_0)
% 0.54/0.75          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['39'])).
% 0.54/0.75  thf('41', plain,
% 0.54/0.75      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.54/0.75        | (r2_hidden @ 
% 0.54/0.75           (k4_tarski @ (sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75            (sk_E @ (sk_B_1 @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.54/0.75           k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['0', '40'])).
% 0.54/0.75  thf(t7_ordinal1, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.75  thf('42', plain,
% 0.54/0.75      (![X19 : $i, X20 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.54/0.75  thf('43', plain,
% 0.54/0.75      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.54/0.75        | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.54/0.75             (k4_tarski @ (sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.54/0.75              (sk_E @ (sk_B_1 @ (k1_tarski @ sk_A)) @ k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['41', '42'])).
% 0.54/0.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.75  thf('44', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf('45', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['43', '44'])).
% 0.54/0.75  thf(t69_enumset1, axiom,
% 0.54/0.75    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.75  thf('46', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.75  thf(fc3_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.54/0.75  thf('47', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X7 @ X8))),
% 0.54/0.75      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.54/0.75  thf('48', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['46', '47'])).
% 0.54/0.75  thf('49', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['45', '48'])).
% 0.54/0.75  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf(existence_m1_subset_1, axiom,
% 0.54/0.75    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.54/0.75  thf('51', plain, (![X9 : $i]: (m1_subset_1 @ (sk_B @ X9) @ X9)),
% 0.54/0.75      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.54/0.75  thf(t2_subset, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ A @ B ) =>
% 0.54/0.75       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.54/0.75  thf('52', plain,
% 0.54/0.75      (![X14 : $i, X15 : $i]:
% 0.54/0.75         ((r2_hidden @ X14 @ X15)
% 0.54/0.75          | (v1_xboole_0 @ X15)
% 0.54/0.75          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_subset])).
% 0.54/0.75  thf('53', plain,
% 0.54/0.75      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['51', '52'])).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      (![X19 : $i, X20 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.54/0.75  thf('55', plain,
% 0.54/0.75      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['50', '55'])).
% 0.54/0.75  thf('57', plain, ($false), inference('demod', [status(thm)], ['49', '56'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
