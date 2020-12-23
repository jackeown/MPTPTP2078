%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hDFdQryEJl

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:13 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 605 expanded)
%              Number of leaves         :   34 ( 182 expanded)
%              Depth                    :   20
%              Number of atoms          :  946 (8801 expanded)
%              Number of equality atoms :   77 ( 551 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,negated_conjecture,(
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

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('3',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['31'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X25 ) @ X26 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['19','20'])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['39'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('57',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','60'])).

thf('62',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('66',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['39'])).

thf('67',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','61'])).

thf('70',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['31'])).

thf('71',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( v1_funct_2 @ X25 @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['19','20'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('75',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('78',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['39'])).

thf('79',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('82',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('83',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('84',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['39'])).

thf('86',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('88',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['39'])).

thf('91',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['43','68','80','81','89','90'])).

thf('92',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['40','91'])).

thf('93',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','92'])).

thf('94',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('95',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['43','68','80','90','81'])).

thf('96',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['93','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hDFdQryEJl
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:04:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.81  % Solved by: fo/fo7.sh
% 0.59/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.81  % done 402 iterations in 0.348s
% 0.59/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.81  % SZS output start Refutation
% 0.59/0.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.81  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.59/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.59/0.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.81  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.81  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.81  thf(d1_funct_2, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.81       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.81           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.59/0.81             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.59/0.81         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.81           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.59/0.81             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_0, axiom,
% 0.59/0.81    (![B:$i,A:$i]:
% 0.59/0.81     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.81       ( zip_tseitin_0 @ B @ A ) ))).
% 0.59/0.81  thf('0', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i]:
% 0.59/0.81         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(t9_funct_2, conjecture,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.59/0.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.81       ( ( r1_tarski @ B @ C ) =>
% 0.59/0.81         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.59/0.81           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.59/0.81             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_1, negated_conjecture,
% 0.59/0.81    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.59/0.81            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.81          ( ( r1_tarski @ B @ C ) =>
% 0.59/0.81            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.59/0.81              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.59/0.81                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.59/0.81    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.59/0.81  thf('1', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.59/0.81  thf(zf_stmt_3, axiom,
% 0.59/0.81    (![C:$i,B:$i,A:$i]:
% 0.59/0.81     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.59/0.81       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.59/0.81  thf(zf_stmt_5, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.81       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.59/0.81         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.81           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.59/0.81  thf('2', plain,
% 0.59/0.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.81         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.59/0.81          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.59/0.81          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.81  thf('3', plain,
% 0.59/0.81      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.81  thf('4', plain,
% 0.59/0.81      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['0', '3'])).
% 0.59/0.81  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf('6', plain,
% 0.59/0.81      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.81         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.59/0.81          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.59/0.81          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.81  thf('7', plain,
% 0.59/0.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.59/0.81        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.81  thf('8', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf(redefinition_k1_relset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.81       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.59/0.81  thf('9', plain,
% 0.59/0.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.81         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.59/0.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.81  thf('10', plain,
% 0.59/0.81      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.59/0.81      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.81  thf('11', plain,
% 0.59/0.81      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.59/0.81      inference('demod', [status(thm)], ['7', '10'])).
% 0.59/0.81  thf('12', plain,
% 0.59/0.81      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['4', '11'])).
% 0.59/0.81  thf(d3_tarski, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.81  thf('13', plain,
% 0.59/0.81      (![X1 : $i, X3 : $i]:
% 0.59/0.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.81  thf('14', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf(cc2_relset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.81  thf('15', plain,
% 0.59/0.81      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.81         ((v5_relat_1 @ X11 @ X13)
% 0.59/0.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.59/0.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.81  thf('16', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.59/0.81      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.81  thf(d19_relat_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( v1_relat_1 @ B ) =>
% 0.59/0.81       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.59/0.81  thf('17', plain,
% 0.59/0.81      (![X6 : $i, X7 : $i]:
% 0.59/0.81         (~ (v5_relat_1 @ X6 @ X7)
% 0.59/0.81          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.59/0.81          | ~ (v1_relat_1 @ X6))),
% 0.59/0.81      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.59/0.81  thf('18', plain,
% 0.59/0.81      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.81  thf('19', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf(cc1_relset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.81       ( v1_relat_1 @ C ) ))).
% 0.59/0.81  thf('20', plain,
% 0.59/0.81      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.81         ((v1_relat_1 @ X8)
% 0.59/0.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.59/0.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.81  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.81  thf('22', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.59/0.81      inference('demod', [status(thm)], ['18', '21'])).
% 0.59/0.81  thf('23', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.81          | (r2_hidden @ X0 @ X2)
% 0.59/0.81          | ~ (r1_tarski @ X1 @ X2))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.81  thf('24', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.59/0.81  thf('25', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.59/0.81          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_D)) @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['13', '24'])).
% 0.59/0.81  thf('26', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf('27', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.81          | (r2_hidden @ X0 @ X2)
% 0.59/0.81          | ~ (r1_tarski @ X1 @ X2))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.81  thf('28', plain,
% 0.59/0.81      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.81  thf('29', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.59/0.81          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_D)) @ sk_C_1))),
% 0.59/0.81      inference('sup-', [status(thm)], ['25', '28'])).
% 0.59/0.81  thf('30', plain,
% 0.59/0.81      (![X1 : $i, X3 : $i]:
% 0.59/0.81         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.81  thf('31', plain,
% 0.59/0.81      (((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)
% 0.59/0.81        | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1))),
% 0.59/0.81      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.81  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.59/0.81      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.81  thf(t4_funct_2, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.81       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.59/0.81         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.59/0.81           ( m1_subset_1 @
% 0.59/0.81             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.59/0.81  thf('33', plain,
% 0.59/0.81      (![X25 : $i, X26 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.59/0.81          | (m1_subset_1 @ X25 @ 
% 0.59/0.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X25) @ X26)))
% 0.59/0.81          | ~ (v1_funct_1 @ X25)
% 0.59/0.81          | ~ (v1_relat_1 @ X25))),
% 0.59/0.81      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.59/0.81  thf('34', plain,
% 0.59/0.81      ((~ (v1_relat_1 @ sk_D)
% 0.59/0.81        | ~ (v1_funct_1 @ sk_D)
% 0.59/0.81        | (m1_subset_1 @ sk_D @ 
% 0.59/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.81  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.81  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf('37', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ 
% 0.59/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))),
% 0.59/0.81      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.59/0.81  thf('38', plain,
% 0.59/0.81      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['12', '37'])).
% 0.59/0.81  thf('39', plain,
% 0.59/0.81      ((~ (v1_funct_1 @ sk_D)
% 0.59/0.81        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.59/0.81        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf('40', plain,
% 0.59/0.81      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.59/0.81         <= (~
% 0.59/0.81             ((m1_subset_1 @ sk_D @ 
% 0.59/0.81               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.59/0.81      inference('split', [status(esa)], ['39'])).
% 0.59/0.81  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf('42', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.59/0.81      inference('split', [status(esa)], ['39'])).
% 0.59/0.81  thf('43', plain, (((v1_funct_1 @ sk_D))),
% 0.59/0.81      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.81  thf('44', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf('45', plain,
% 0.59/0.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('split', [status(esa)], ['44'])).
% 0.59/0.81  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf('47', plain,
% 0.59/0.81      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.59/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['45', '46'])).
% 0.59/0.81  thf('48', plain,
% 0.59/0.81      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.81         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.59/0.81          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.59/0.81          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.81  thf('49', plain,
% 0.59/0.81      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.59/0.81         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.59/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['47', '48'])).
% 0.59/0.81  thf('50', plain,
% 0.59/0.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('split', [status(esa)], ['44'])).
% 0.59/0.81  thf('51', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf('52', plain,
% 0.59/0.81      (((m1_subset_1 @ sk_D @ 
% 0.59/0.81         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.59/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['50', '51'])).
% 0.59/0.81  thf('53', plain,
% 0.59/0.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.81         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.59/0.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.81  thf('54', plain,
% 0.59/0.81      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.59/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.81  thf('55', plain,
% 0.59/0.81      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.59/0.81         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 0.59/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['49', '54'])).
% 0.59/0.81  thf('56', plain,
% 0.59/0.81      (((m1_subset_1 @ sk_D @ 
% 0.59/0.81         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.59/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['50', '51'])).
% 0.59/0.81  thf('57', plain,
% 0.59/0.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.81         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.59/0.81          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.59/0.81          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.81  thf('58', plain,
% 0.59/0.81      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.59/0.81         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.59/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['56', '57'])).
% 0.59/0.81  thf('59', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i]:
% 0.59/0.81         ((zip_tseitin_0 @ X17 @ X18) | ((X18) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('60', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 0.59/0.81      inference('simplify', [status(thm)], ['59'])).
% 0.59/0.81  thf('61', plain,
% 0.59/0.81      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.59/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['58', '60'])).
% 0.59/0.81  thf('62', plain,
% 0.59/0.81      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['55', '61'])).
% 0.59/0.81  thf('63', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ 
% 0.59/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))),
% 0.59/0.81      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.59/0.81  thf('64', plain,
% 0.59/0.81      (((m1_subset_1 @ sk_D @ 
% 0.59/0.81         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.59/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['62', '63'])).
% 0.59/0.81  thf('65', plain,
% 0.59/0.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('split', [status(esa)], ['44'])).
% 0.59/0.81  thf('66', plain,
% 0.59/0.81      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.59/0.81         <= (~
% 0.59/0.81             ((m1_subset_1 @ sk_D @ 
% 0.59/0.81               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.59/0.81      inference('split', [status(esa)], ['39'])).
% 0.59/0.81  thf('67', plain,
% 0.59/0.81      ((~ (m1_subset_1 @ sk_D @ 
% 0.59/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.59/0.81         <= (~
% 0.59/0.81             ((m1_subset_1 @ sk_D @ 
% 0.59/0.81               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.59/0.81             (((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['65', '66'])).
% 0.59/0.81  thf('68', plain,
% 0.59/0.81      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.59/0.81       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['64', '67'])).
% 0.59/0.81  thf('69', plain,
% 0.59/0.81      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['55', '61'])).
% 0.59/0.81  thf('70', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.59/0.81      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.81  thf('71', plain,
% 0.59/0.81      (![X25 : $i, X26 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.59/0.81          | (v1_funct_2 @ X25 @ (k1_relat_1 @ X25) @ X26)
% 0.59/0.81          | ~ (v1_funct_1 @ X25)
% 0.59/0.81          | ~ (v1_relat_1 @ X25))),
% 0.59/0.81      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.59/0.81  thf('72', plain,
% 0.59/0.81      ((~ (v1_relat_1 @ sk_D)
% 0.59/0.81        | ~ (v1_funct_1 @ sk_D)
% 0.59/0.81        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C_1))),
% 0.59/0.81      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.81  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.81  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.81  thf('75', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C_1)),
% 0.59/0.81      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.59/0.81  thf('76', plain,
% 0.59/0.81      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.59/0.81         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['69', '75'])).
% 0.59/0.81  thf('77', plain,
% 0.59/0.81      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('split', [status(esa)], ['44'])).
% 0.59/0.81  thf('78', plain,
% 0.59/0.81      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.59/0.81         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.59/0.81      inference('split', [status(esa)], ['39'])).
% 0.59/0.81  thf('79', plain,
% 0.59/0.81      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.59/0.81         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.59/0.81             (((sk_A) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['77', '78'])).
% 0.59/0.81  thf('80', plain,
% 0.59/0.81      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['76', '79'])).
% 0.59/0.81  thf('81', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('split', [status(esa)], ['44'])).
% 0.59/0.81  thf('82', plain,
% 0.59/0.81      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['4', '11'])).
% 0.59/0.81  thf('83', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C_1)),
% 0.59/0.81      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.59/0.81  thf('84', plain,
% 0.59/0.81      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1) | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['82', '83'])).
% 0.59/0.81  thf('85', plain,
% 0.59/0.81      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.59/0.81         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.59/0.81      inference('split', [status(esa)], ['39'])).
% 0.59/0.81  thf('86', plain,
% 0.59/0.81      ((((sk_B) = (k1_xboole_0))) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['84', '85'])).
% 0.59/0.81  thf('87', plain,
% 0.59/0.81      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('split', [status(esa)], ['44'])).
% 0.59/0.81  thf('88', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.59/0.81         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.59/0.81             ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['86', '87'])).
% 0.59/0.81  thf('89', plain,
% 0.59/0.81      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | (((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['88'])).
% 0.59/0.81  thf('90', plain,
% 0.59/0.81      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.59/0.81       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 0.59/0.81      inference('split', [status(esa)], ['39'])).
% 0.59/0.81  thf('91', plain,
% 0.59/0.81      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.59/0.81      inference('sat_resolution*', [status(thm)],
% 0.59/0.81                ['43', '68', '80', '81', '89', '90'])).
% 0.59/0.81  thf('92', plain,
% 0.59/0.81      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.59/0.81      inference('simpl_trail', [status(thm)], ['40', '91'])).
% 0.59/0.81  thf('93', plain, (((sk_B) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['38', '92'])).
% 0.59/0.81  thf('94', plain,
% 0.59/0.81      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('split', [status(esa)], ['44'])).
% 0.59/0.81  thf('95', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sat_resolution*', [status(thm)],
% 0.59/0.81                ['43', '68', '80', '90', '81'])).
% 0.59/0.81  thf('96', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.81      inference('simpl_trail', [status(thm)], ['94', '95'])).
% 0.59/0.81  thf('97', plain, ($false),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['93', '96'])).
% 0.59/0.81  
% 0.59/0.81  % SZS output end Refutation
% 0.59/0.81  
% 0.59/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
