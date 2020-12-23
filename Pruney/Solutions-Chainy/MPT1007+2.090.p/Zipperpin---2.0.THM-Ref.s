%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hGf4yEyTsX

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:28 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 225 expanded)
%              Number of leaves         :   43 (  87 expanded)
%              Depth                    :   24
%              Number of atoms          :  811 (2294 expanded)
%              Number of equality atoms :   50 ( 115 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X31 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

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

thf('2',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X31 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_mcart_1 @ X29 )
        = X28 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ ( k1_tarski @ X28 ) @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('8',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('11',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B_1 @ sk_C ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X48 @ X45 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(demod,[status(thm)],['1','24'])).

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

thf('26',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X31 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('33',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['22','23'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B_2 @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('39',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('42',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('45',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_2 @ X0 ) ),
    inference(demod,[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('54',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ X0 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','56'])).

thf('58',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
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

thf('59',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X22 )
       != X20 )
      | ~ ( r2_hidden @ X23 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( sk_E @ X23 @ X22 ) ) @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','62'])).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('65',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('67',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hGf4yEyTsX
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:09:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.58/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.85  % Solved by: fo/fo7.sh
% 0.58/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.85  % done 520 iterations in 0.420s
% 0.58/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.85  % SZS output start Refutation
% 0.58/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.85  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.85  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.58/0.85  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.85  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.58/0.85  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.58/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.85  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.58/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.85  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.85  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.58/0.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.85  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.58/0.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.58/0.85  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.58/0.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.85  thf(t6_mcart_1, axiom,
% 0.58/0.85    (![A:$i]:
% 0.58/0.85     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.85          ( ![B:$i]:
% 0.58/0.85            ( ~( ( r2_hidden @ B @ A ) & 
% 0.58/0.85                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.58/0.85                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.58/0.85                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.58/0.85                       ( r2_hidden @ G @ B ) ) =>
% 0.58/0.85                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.58/0.85  thf('0', plain,
% 0.58/0.85      (![X31 : $i]:
% 0.58/0.85         (((X31) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X31) @ X31))),
% 0.58/0.85      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.58/0.85  thf(t61_funct_2, conjecture,
% 0.58/0.85    (![A:$i,B:$i,C:$i]:
% 0.58/0.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.58/0.85         ( m1_subset_1 @
% 0.58/0.85           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.58/0.85       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.58/0.85         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.58/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.85        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.58/0.85            ( m1_subset_1 @
% 0.58/0.85              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.58/0.85          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.58/0.85            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.58/0.85    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.58/0.85  thf('1', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf('2', plain,
% 0.58/0.85      (![X31 : $i]:
% 0.58/0.85         (((X31) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X31) @ X31))),
% 0.58/0.85      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.58/0.85  thf('3', plain,
% 0.58/0.85      ((m1_subset_1 @ sk_C @ 
% 0.58/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf(l3_subset_1, axiom,
% 0.58/0.85    (![A:$i,B:$i]:
% 0.58/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.85       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.58/0.85  thf('4', plain,
% 0.58/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.85         (~ (r2_hidden @ X9 @ X10)
% 0.58/0.85          | (r2_hidden @ X9 @ X11)
% 0.58/0.85          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.58/0.85      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.58/0.85  thf('5', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.58/0.85          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.58/0.85      inference('sup-', [status(thm)], ['3', '4'])).
% 0.58/0.85  thf('6', plain,
% 0.58/0.85      ((((sk_C) = (k1_xboole_0))
% 0.58/0.85        | (r2_hidden @ (sk_B_1 @ sk_C) @ 
% 0.58/0.85           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['2', '5'])).
% 0.58/0.85  thf(t12_mcart_1, axiom,
% 0.58/0.85    (![A:$i,B:$i,C:$i]:
% 0.58/0.85     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.58/0.85       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.58/0.85         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.58/0.85  thf('7', plain,
% 0.58/0.85      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.85         (((k1_mcart_1 @ X29) = (X28))
% 0.58/0.85          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ (k1_tarski @ X28) @ X30)))),
% 0.58/0.85      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.58/0.85  thf('8', plain,
% 0.58/0.85      ((((sk_C) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B_1 @ sk_C)) = (sk_A)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.85  thf('9', plain,
% 0.58/0.85      ((((sk_C) = (k1_xboole_0))
% 0.58/0.85        | (r2_hidden @ (sk_B_1 @ sk_C) @ 
% 0.58/0.85           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['2', '5'])).
% 0.58/0.85  thf(t10_mcart_1, axiom,
% 0.58/0.85    (![A:$i,B:$i,C:$i]:
% 0.58/0.85     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.58/0.85       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.58/0.85         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.58/0.85  thf('10', plain,
% 0.58/0.85      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.85         ((r2_hidden @ (k1_mcart_1 @ X25) @ X26)
% 0.58/0.85          | ~ (r2_hidden @ X25 @ (k2_zfmisc_1 @ X26 @ X27)))),
% 0.58/0.85      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.58/0.85  thf('11', plain,
% 0.58/0.85      ((((sk_C) = (k1_xboole_0))
% 0.58/0.85        | (r2_hidden @ (k1_mcart_1 @ (sk_B_1 @ sk_C)) @ (k1_tarski @ sk_A)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.85  thf('12', plain,
% 0.58/0.85      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.58/0.85        | ((sk_C) = (k1_xboole_0))
% 0.58/0.85        | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.85      inference('sup+', [status(thm)], ['8', '11'])).
% 0.58/0.85  thf('13', plain,
% 0.58/0.85      ((((sk_C) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.58/0.85      inference('simplify', [status(thm)], ['12'])).
% 0.58/0.85  thf('14', plain,
% 0.58/0.85      ((m1_subset_1 @ sk_C @ 
% 0.58/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf(t7_funct_2, axiom,
% 0.58/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.85     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.85       ( ( r2_hidden @ C @ A ) =>
% 0.58/0.85         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.85           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.58/0.85  thf('15', plain,
% 0.58/0.85      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.58/0.85         (~ (r2_hidden @ X45 @ X46)
% 0.58/0.85          | ((X47) = (k1_xboole_0))
% 0.58/0.85          | ~ (v1_funct_1 @ X48)
% 0.58/0.85          | ~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.58/0.85          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.58/0.85          | (r2_hidden @ (k1_funct_1 @ X48 @ X45) @ X47))),
% 0.58/0.85      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.58/0.85  thf('16', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.58/0.85          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.58/0.85          | ~ (v1_funct_1 @ sk_C)
% 0.58/0.85          | ((sk_B_2) = (k1_xboole_0))
% 0.58/0.85          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.85  thf('17', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf('19', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.58/0.85          | ((sk_B_2) = (k1_xboole_0))
% 0.58/0.85          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.85      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.58/0.85  thf('20', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf('21', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.58/0.85          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.85      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.58/0.85  thf('22', plain,
% 0.58/0.85      ((((sk_C) = (k1_xboole_0))
% 0.58/0.85        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2))),
% 0.58/0.85      inference('sup-', [status(thm)], ['13', '21'])).
% 0.58/0.85  thf('23', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_2)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.85  thf('24', plain, (((sk_C) = (k1_xboole_0))),
% 0.58/0.85      inference('clc', [status(thm)], ['22', '23'])).
% 0.58/0.85  thf('25', plain, ((v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.58/0.85      inference('demod', [status(thm)], ['1', '24'])).
% 0.58/0.85  thf(d1_funct_2, axiom,
% 0.58/0.85    (![A:$i,B:$i,C:$i]:
% 0.58/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.85       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.85           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.85             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.85         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.85           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.85             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.85  thf(zf_stmt_1, axiom,
% 0.58/0.85    (![C:$i,B:$i,A:$i]:
% 0.58/0.85     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.58/0.85       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.85  thf('26', plain,
% 0.58/0.85      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.58/0.85         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 0.58/0.85          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 0.58/0.85          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.85  thf('27', plain,
% 0.58/0.85      ((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.58/0.85        | ((k1_tarski @ sk_A)
% 0.58/0.85            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.85  thf(zf_stmt_2, axiom,
% 0.58/0.85    (![B:$i,A:$i]:
% 0.58/0.85     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.85       ( zip_tseitin_0 @ B @ A ) ))).
% 0.58/0.85  thf('28', plain,
% 0.58/0.85      (![X37 : $i, X38 : $i]:
% 0.58/0.85         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.85  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.85  thf('29', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.85  thf('30', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.85         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.58/0.85      inference('sup+', [status(thm)], ['28', '29'])).
% 0.58/0.85  thf('31', plain,
% 0.58/0.85      (![X31 : $i]:
% 0.58/0.85         (((X31) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X31) @ X31))),
% 0.58/0.85      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.58/0.85  thf('32', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_2)
% 0.58/0.85          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.85      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.58/0.85  thf('33', plain, (((sk_C) = (k1_xboole_0))),
% 0.58/0.85      inference('clc', [status(thm)], ['22', '23'])).
% 0.58/0.85  thf('34', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X0) @ sk_B_2)
% 0.58/0.85          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.85      inference('demod', [status(thm)], ['32', '33'])).
% 0.58/0.85  thf('35', plain,
% 0.58/0.85      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.58/0.85        | (r2_hidden @ 
% 0.58/0.85           (k1_funct_1 @ k1_xboole_0 @ (sk_B_1 @ (k1_tarski @ sk_A))) @ sk_B_2))),
% 0.58/0.85      inference('sup-', [status(thm)], ['31', '34'])).
% 0.58/0.85  thf(t7_ordinal1, axiom,
% 0.58/0.85    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.85  thf('36', plain,
% 0.58/0.85      (![X18 : $i, X19 : $i]:
% 0.58/0.85         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.58/0.85      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.85  thf('37', plain,
% 0.58/0.85      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.58/0.85        | ~ (r1_tarski @ sk_B_2 @ 
% 0.58/0.85             (k1_funct_1 @ k1_xboole_0 @ (sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.58/0.85      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.85  thf('38', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((zip_tseitin_0 @ sk_B_2 @ X0) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['30', '37'])).
% 0.58/0.85  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.58/0.85  thf('39', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.58/0.85      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.58/0.85  thf('40', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (v1_xboole_0 @ k1_xboole_0) | (zip_tseitin_0 @ sk_B_2 @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.85  thf('41', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.85  thf(existence_m1_subset_1, axiom,
% 0.58/0.85    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.58/0.85  thf('42', plain, (![X8 : $i]: (m1_subset_1 @ (sk_B @ X8) @ X8)),
% 0.58/0.85      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.58/0.85  thf(t2_subset, axiom,
% 0.58/0.85    (![A:$i,B:$i]:
% 0.58/0.85     ( ( m1_subset_1 @ A @ B ) =>
% 0.58/0.85       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.58/0.85  thf('43', plain,
% 0.58/0.85      (![X13 : $i, X14 : $i]:
% 0.58/0.85         ((r2_hidden @ X13 @ X14)
% 0.58/0.85          | (v1_xboole_0 @ X14)
% 0.58/0.85          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.58/0.85      inference('cnf', [status(esa)], [t2_subset])).
% 0.58/0.85  thf('44', plain,
% 0.58/0.85      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.85  thf(t4_subset_1, axiom,
% 0.58/0.85    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.85  thf('45', plain,
% 0.58/0.85      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.58/0.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.85  thf('46', plain,
% 0.58/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.85         (~ (r2_hidden @ X9 @ X10)
% 0.58/0.85          | (r2_hidden @ X9 @ X11)
% 0.58/0.85          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.58/0.85      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.58/0.85  thf('47', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['45', '46'])).
% 0.58/0.85  thf('48', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['44', '47'])).
% 0.58/0.85  thf('49', plain,
% 0.58/0.85      (![X18 : $i, X19 : $i]:
% 0.58/0.85         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.58/0.85      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.85  thf('50', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((v1_xboole_0 @ k1_xboole_0)
% 0.58/0.85          | ~ (r1_tarski @ X0 @ (sk_B @ k1_xboole_0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.85  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.85      inference('sup-', [status(thm)], ['41', '50'])).
% 0.58/0.85  thf('52', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_2 @ X0)),
% 0.58/0.85      inference('demod', [status(thm)], ['40', '51'])).
% 0.58/0.85  thf('53', plain,
% 0.58/0.85      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.58/0.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.85  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.58/0.85  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.58/0.85  thf(zf_stmt_5, axiom,
% 0.58/0.85    (![A:$i,B:$i,C:$i]:
% 0.58/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.85       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.58/0.85         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.85           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.85             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.85  thf('54', plain,
% 0.58/0.85      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.58/0.85         (~ (zip_tseitin_0 @ X42 @ X43)
% 0.58/0.85          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 0.58/0.85          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.85  thf('55', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.58/0.85      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.85  thf('56', plain, (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ X0)),
% 0.58/0.85      inference('sup-', [status(thm)], ['52', '55'])).
% 0.58/0.85  thf('57', plain,
% 0.58/0.85      (((k1_tarski @ sk_A)
% 0.58/0.85         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0))),
% 0.58/0.85      inference('demod', [status(thm)], ['27', '56'])).
% 0.58/0.85  thf('58', plain,
% 0.58/0.85      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.58/0.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.85  thf(t22_relset_1, axiom,
% 0.58/0.85    (![A:$i,B:$i,C:$i]:
% 0.58/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.58/0.85       ( ( ![D:$i]:
% 0.58/0.85           ( ~( ( r2_hidden @ D @ B ) & 
% 0.58/0.85                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.58/0.85         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.58/0.85  thf('59', plain,
% 0.58/0.85      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.85         (((k1_relset_1 @ X20 @ X21 @ X22) != (X20))
% 0.58/0.85          | ~ (r2_hidden @ X23 @ X20)
% 0.58/0.85          | (r2_hidden @ (k4_tarski @ X23 @ (sk_E @ X23 @ X22)) @ X22)
% 0.58/0.85          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.58/0.85      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.58/0.85  thf('60', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.85         ((r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 0.58/0.85           k1_xboole_0)
% 0.58/0.85          | ~ (r2_hidden @ X2 @ X1)
% 0.58/0.85          | ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) != (X1)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.85  thf('61', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.58/0.85          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.58/0.85          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.58/0.85             k1_xboole_0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['57', '60'])).
% 0.58/0.85  thf('62', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.58/0.85           k1_xboole_0)
% 0.58/0.85          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.85      inference('simplify', [status(thm)], ['61'])).
% 0.58/0.85  thf('63', plain,
% 0.58/0.85      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.58/0.85        | (r2_hidden @ 
% 0.58/0.85           (k4_tarski @ (sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.58/0.85            (sk_E @ (sk_B_1 @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.58/0.85           k1_xboole_0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['0', '62'])).
% 0.58/0.85  thf('64', plain,
% 0.58/0.85      (![X18 : $i, X19 : $i]:
% 0.58/0.85         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.58/0.85      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.85  thf('65', plain,
% 0.58/0.85      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.58/0.85        | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.58/0.85             (k4_tarski @ (sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.58/0.85              (sk_E @ (sk_B_1 @ (k1_tarski @ sk_A)) @ k1_xboole_0))))),
% 0.58/0.85      inference('sup-', [status(thm)], ['63', '64'])).
% 0.58/0.85  thf('66', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.85  thf('67', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.58/0.85      inference('demod', [status(thm)], ['65', '66'])).
% 0.58/0.85  thf('68', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.58/0.85      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.58/0.85  thf('69', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.85      inference('sup-', [status(thm)], ['67', '68'])).
% 0.58/0.85  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.85      inference('sup-', [status(thm)], ['41', '50'])).
% 0.58/0.85  thf('71', plain, ($false), inference('demod', [status(thm)], ['69', '70'])).
% 0.58/0.85  
% 0.58/0.85  % SZS output end Refutation
% 0.58/0.85  
% 0.58/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
