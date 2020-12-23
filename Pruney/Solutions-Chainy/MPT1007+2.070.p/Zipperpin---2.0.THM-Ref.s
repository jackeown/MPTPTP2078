%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HKLdRowIgg

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:25 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 168 expanded)
%              Number of leaves         :   47 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  692 (1623 expanded)
%              Number of equality atoms :   51 (  96 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('0',plain,(
    v1_funct_2 @ sk_C_2 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
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

thf('1',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( v1_funct_2 @ X61 @ X59 @ X60 )
      | ( X59
        = ( k1_relset_1 @ X59 @ X60 @ X61 ) )
      | ~ ( zip_tseitin_1 @ X61 @ X60 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k1_relset_1 @ X43 @ X44 @ X42 )
        = ( k1_relat_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('5',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X57: $i,X58: $i] :
      ( ( zip_tseitin_0 @ X57 @ X58 )
      | ( X57 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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

thf('9',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( zip_tseitin_0 @ X62 @ X63 )
      | ( zip_tseitin_1 @ X64 @ X62 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','13'])).

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

thf('15',plain,(
    ! [X51: $i] :
      ( ( X51 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X51 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('22',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k1_mcart_1 @ X49 )
        = X48 )
      | ~ ( r2_hidden @ X49 @ ( k2_zfmisc_1 @ ( k1_tarski @ X48 ) @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('23',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B @ sk_C_2 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('25',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X45 ) @ X46 )
      | ~ ( r2_hidden @ X45 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('26',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ sk_C_2 ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('30',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('31',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k1_relat_1 @ X38 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X38 @ X37 ) @ ( k2_relat_1 @ X38 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('32',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X35: $i,X36: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['32','37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v5_relat_1 @ X39 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['40','41'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('43',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v5_relat_1 @ X33 @ X34 )
      | ( r1_tarski @ ( k2_relat_1 @ X33 ) @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['35','36'])).

thf('46',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('52',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','51','52'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HKLdRowIgg
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 12:59:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.66/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.91  % Solved by: fo/fo7.sh
% 0.66/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.91  % done 343 iterations in 0.439s
% 0.66/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.91  % SZS output start Refutation
% 0.66/0.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.66/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.66/0.91  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.66/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.91  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.66/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.66/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.91  thf(sk_B_type, type, sk_B: $i > $i).
% 0.66/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.91  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.66/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.91  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.66/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.91  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.66/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.91  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.66/0.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.66/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.91  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.66/0.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.66/0.91  thf(t61_funct_2, conjecture,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.66/0.91         ( m1_subset_1 @
% 0.66/0.91           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.66/0.91       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.66/0.91         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.66/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.91    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.66/0.91            ( m1_subset_1 @
% 0.66/0.91              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.66/0.91          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.66/0.91            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.66/0.91    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.66/0.91  thf('0', plain, ((v1_funct_2 @ sk_C_2 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf(d1_funct_2, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.66/0.91           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.66/0.91             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.66/0.91         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.66/0.91           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.66/0.91             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.66/0.91  thf(zf_stmt_1, axiom,
% 0.66/0.91    (![C:$i,B:$i,A:$i]:
% 0.66/0.91     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.66/0.91       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.66/0.91  thf('1', plain,
% 0.66/0.91      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.66/0.91         (~ (v1_funct_2 @ X61 @ X59 @ X60)
% 0.66/0.91          | ((X59) = (k1_relset_1 @ X59 @ X60 @ X61))
% 0.66/0.91          | ~ (zip_tseitin_1 @ X61 @ X60 @ X59))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.91  thf('2', plain,
% 0.66/0.91      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.66/0.91        | ((k1_tarski @ sk_A)
% 0.66/0.91            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_2)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['0', '1'])).
% 0.66/0.91  thf('3', plain,
% 0.66/0.91      ((m1_subset_1 @ sk_C_2 @ 
% 0.66/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf(redefinition_k1_relset_1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.91       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.66/0.91  thf('4', plain,
% 0.66/0.91      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.66/0.91         (((k1_relset_1 @ X43 @ X44 @ X42) = (k1_relat_1 @ X42))
% 0.66/0.91          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.66/0.91      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.66/0.91  thf('5', plain,
% 0.66/0.91      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_2)
% 0.66/0.91         = (k1_relat_1 @ sk_C_2))),
% 0.66/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.66/0.91  thf('6', plain,
% 0.66/0.91      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.66/0.91        | ((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.66/0.91      inference('demod', [status(thm)], ['2', '5'])).
% 0.66/0.91  thf(zf_stmt_2, axiom,
% 0.66/0.91    (![B:$i,A:$i]:
% 0.66/0.91     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.66/0.91       ( zip_tseitin_0 @ B @ A ) ))).
% 0.66/0.91  thf('7', plain,
% 0.66/0.91      (![X57 : $i, X58 : $i]:
% 0.66/0.91         ((zip_tseitin_0 @ X57 @ X58) | ((X57) = (k1_xboole_0)))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.91  thf('8', plain,
% 0.66/0.91      ((m1_subset_1 @ sk_C_2 @ 
% 0.66/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.66/0.91  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.66/0.91  thf(zf_stmt_5, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.91       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.66/0.91         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.66/0.91           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.66/0.91             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.66/0.91  thf('9', plain,
% 0.66/0.91      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.66/0.91         (~ (zip_tseitin_0 @ X62 @ X63)
% 0.66/0.91          | (zip_tseitin_1 @ X64 @ X62 @ X63)
% 0.66/0.91          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X62))))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.66/0.91  thf('10', plain,
% 0.66/0.91      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.66/0.91        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['8', '9'])).
% 0.66/0.91  thf('11', plain,
% 0.66/0.91      ((((sk_B_1) = (k1_xboole_0))
% 0.66/0.91        | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['7', '10'])).
% 0.66/0.91  thf('12', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('13', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.66/0.91      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.66/0.91  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.66/0.91      inference('demod', [status(thm)], ['6', '13'])).
% 0.66/0.91  thf(t6_mcart_1, axiom,
% 0.66/0.91    (![A:$i]:
% 0.66/0.91     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.66/0.91          ( ![B:$i]:
% 0.66/0.91            ( ~( ( r2_hidden @ B @ A ) & 
% 0.66/0.91                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.66/0.91                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.66/0.91                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.66/0.91                       ( r2_hidden @ G @ B ) ) =>
% 0.66/0.91                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.66/0.91  thf('15', plain,
% 0.66/0.91      (![X51 : $i]:
% 0.66/0.91         (((X51) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X51) @ X51))),
% 0.66/0.91      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.66/0.91  thf('16', plain,
% 0.66/0.91      ((m1_subset_1 @ sk_C_2 @ 
% 0.66/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf(t3_subset, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.66/0.91  thf('17', plain,
% 0.66/0.91      (![X28 : $i, X29 : $i]:
% 0.66/0.91         ((r1_tarski @ X28 @ X29) | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.66/0.91  thf('18', plain,
% 0.66/0.91      ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.66/0.91      inference('sup-', [status(thm)], ['16', '17'])).
% 0.66/0.91  thf(d3_tarski, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( r1_tarski @ A @ B ) <=>
% 0.66/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.66/0.91  thf('19', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X0 @ X1)
% 0.66/0.91          | (r2_hidden @ X0 @ X2)
% 0.66/0.91          | ~ (r1_tarski @ X1 @ X2))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf('20', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.66/0.91          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.66/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.66/0.91  thf('21', plain,
% 0.66/0.91      ((((sk_C_2) = (k1_xboole_0))
% 0.66/0.91        | (r2_hidden @ (sk_B @ sk_C_2) @ 
% 0.66/0.91           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['15', '20'])).
% 0.66/0.91  thf(t12_mcart_1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.66/0.91       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.66/0.91         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.66/0.91  thf('22', plain,
% 0.66/0.91      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.66/0.91         (((k1_mcart_1 @ X49) = (X48))
% 0.66/0.91          | ~ (r2_hidden @ X49 @ (k2_zfmisc_1 @ (k1_tarski @ X48) @ X50)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.66/0.91  thf('23', plain,
% 0.66/0.91      ((((sk_C_2) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B @ sk_C_2)) = (sk_A)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['21', '22'])).
% 0.66/0.91  thf('24', plain,
% 0.66/0.91      ((((sk_C_2) = (k1_xboole_0))
% 0.66/0.91        | (r2_hidden @ (sk_B @ sk_C_2) @ 
% 0.66/0.91           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['15', '20'])).
% 0.66/0.91  thf(t10_mcart_1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.66/0.91       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.66/0.91         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.66/0.91  thf('25', plain,
% 0.66/0.91      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.66/0.91         ((r2_hidden @ (k1_mcart_1 @ X45) @ X46)
% 0.66/0.91          | ~ (r2_hidden @ X45 @ (k2_zfmisc_1 @ X46 @ X47)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.66/0.91  thf('26', plain,
% 0.66/0.91      ((((sk_C_2) = (k1_xboole_0))
% 0.66/0.91        | (r2_hidden @ (k1_mcart_1 @ (sk_B @ sk_C_2)) @ (k1_tarski @ sk_A)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['24', '25'])).
% 0.66/0.91  thf('27', plain,
% 0.66/0.91      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.66/0.91        | ((sk_C_2) = (k1_xboole_0))
% 0.66/0.91        | ((sk_C_2) = (k1_xboole_0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['23', '26'])).
% 0.66/0.91  thf('28', plain,
% 0.66/0.91      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.66/0.91      inference('simplify', [status(thm)], ['27'])).
% 0.66/0.91  thf('29', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.66/0.91      inference('demod', [status(thm)], ['6', '13'])).
% 0.66/0.91  thf('30', plain,
% 0.66/0.91      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2)))),
% 0.66/0.91      inference('demod', [status(thm)], ['28', '29'])).
% 0.66/0.91  thf(t12_funct_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.66/0.91       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.66/0.91         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.66/0.91  thf('31', plain,
% 0.66/0.91      (![X37 : $i, X38 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X37 @ (k1_relat_1 @ X38))
% 0.66/0.91          | (r2_hidden @ (k1_funct_1 @ X38 @ X37) @ (k2_relat_1 @ X38))
% 0.66/0.91          | ~ (v1_funct_1 @ X38)
% 0.66/0.91          | ~ (v1_relat_1 @ X38))),
% 0.66/0.91      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.66/0.91  thf('32', plain,
% 0.66/0.91      ((((sk_C_2) = (k1_xboole_0))
% 0.66/0.91        | ~ (v1_relat_1 @ sk_C_2)
% 0.66/0.91        | ~ (v1_funct_1 @ sk_C_2)
% 0.66/0.91        | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ (k2_relat_1 @ sk_C_2)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['30', '31'])).
% 0.66/0.91  thf('33', plain,
% 0.66/0.91      ((m1_subset_1 @ sk_C_2 @ 
% 0.66/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf(cc2_relat_1, axiom,
% 0.66/0.91    (![A:$i]:
% 0.66/0.91     ( ( v1_relat_1 @ A ) =>
% 0.66/0.91       ( ![B:$i]:
% 0.66/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.66/0.91  thf('34', plain,
% 0.66/0.91      (![X31 : $i, X32 : $i]:
% 0.66/0.91         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.66/0.91          | (v1_relat_1 @ X31)
% 0.66/0.91          | ~ (v1_relat_1 @ X32))),
% 0.66/0.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.66/0.91  thf('35', plain,
% 0.66/0.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.66/0.91        | (v1_relat_1 @ sk_C_2))),
% 0.66/0.91      inference('sup-', [status(thm)], ['33', '34'])).
% 0.66/0.91  thf(fc6_relat_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.66/0.91  thf('36', plain,
% 0.66/0.91      (![X35 : $i, X36 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X35 @ X36))),
% 0.66/0.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.66/0.91  thf('37', plain, ((v1_relat_1 @ sk_C_2)),
% 0.66/0.91      inference('demod', [status(thm)], ['35', '36'])).
% 0.66/0.91  thf('38', plain, ((v1_funct_1 @ sk_C_2)),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('39', plain,
% 0.66/0.91      ((((sk_C_2) = (k1_xboole_0))
% 0.66/0.91        | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ (k2_relat_1 @ sk_C_2)))),
% 0.66/0.91      inference('demod', [status(thm)], ['32', '37', '38'])).
% 0.66/0.91  thf('40', plain,
% 0.66/0.91      ((m1_subset_1 @ sk_C_2 @ 
% 0.66/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf(cc2_relset_1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.91       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.66/0.91  thf('41', plain,
% 0.66/0.91      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.66/0.91         ((v5_relat_1 @ X39 @ X41)
% 0.66/0.91          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.66/0.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.66/0.91  thf('42', plain, ((v5_relat_1 @ sk_C_2 @ sk_B_1)),
% 0.66/0.91      inference('sup-', [status(thm)], ['40', '41'])).
% 0.66/0.91  thf(d19_relat_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( v1_relat_1 @ B ) =>
% 0.66/0.91       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.66/0.91  thf('43', plain,
% 0.66/0.91      (![X33 : $i, X34 : $i]:
% 0.66/0.91         (~ (v5_relat_1 @ X33 @ X34)
% 0.66/0.91          | (r1_tarski @ (k2_relat_1 @ X33) @ X34)
% 0.66/0.91          | ~ (v1_relat_1 @ X33))),
% 0.66/0.91      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.66/0.91  thf('44', plain,
% 0.66/0.91      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1))),
% 0.66/0.91      inference('sup-', [status(thm)], ['42', '43'])).
% 0.66/0.91  thf('45', plain, ((v1_relat_1 @ sk_C_2)),
% 0.66/0.91      inference('demod', [status(thm)], ['35', '36'])).
% 0.66/0.91  thf('46', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.66/0.91      inference('demod', [status(thm)], ['44', '45'])).
% 0.66/0.91  thf('47', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X0 @ X1)
% 0.66/0.91          | (r2_hidden @ X0 @ X2)
% 0.66/0.91          | ~ (r1_tarski @ X1 @ X2))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf('48', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((r2_hidden @ X0 @ sk_B_1)
% 0.66/0.91          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['46', '47'])).
% 0.66/0.91  thf('49', plain,
% 0.66/0.91      ((((sk_C_2) = (k1_xboole_0))
% 0.66/0.91        | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ sk_B_1))),
% 0.66/0.91      inference('sup-', [status(thm)], ['39', '48'])).
% 0.66/0.91  thf('50', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ sk_B_1)),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('51', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.66/0.91      inference('clc', [status(thm)], ['49', '50'])).
% 0.66/0.91  thf(t60_relat_1, axiom,
% 0.66/0.91    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.66/0.91     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.66/0.91  thf('52', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.91      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.66/0.91  thf('53', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.66/0.91      inference('demod', [status(thm)], ['14', '51', '52'])).
% 0.66/0.91  thf(t1_boole, axiom,
% 0.66/0.91    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.91  thf('54', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.66/0.91      inference('cnf', [status(esa)], [t1_boole])).
% 0.66/0.91  thf(t49_zfmisc_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.66/0.91  thf('55', plain,
% 0.66/0.91      (![X22 : $i, X23 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ (k1_tarski @ X22) @ X23) != (k1_xboole_0))),
% 0.66/0.91      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.66/0.91  thf('56', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['54', '55'])).
% 0.66/0.91  thf('57', plain, ($false),
% 0.66/0.91      inference('simplify_reflect-', [status(thm)], ['53', '56'])).
% 0.66/0.91  
% 0.66/0.91  % SZS output end Refutation
% 0.66/0.91  
% 0.66/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
