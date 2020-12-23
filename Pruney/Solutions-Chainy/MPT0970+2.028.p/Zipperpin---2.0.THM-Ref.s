%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iLUGDEwPJM

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:20 EST 2020

% Result     : Theorem 7.31s
% Output     : Refutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 237 expanded)
%              Number of leaves         :   39 (  87 expanded)
%              Depth                    :   25
%              Number of atoms          :  857 (2853 expanded)
%              Number of equality atoms :   57 ( 187 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('16',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_B )
      | ( X34
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X34: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X34 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

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

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X0 = X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('33',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ k1_xboole_0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('35',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( r1_tarski @ sk_B @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('38',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('46',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('50',plain,
    ( ( k1_xboole_0 != sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['50','55'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X10 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['58','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['23','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['17','71'])).

thf('73',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('74',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','16'])).

thf('76',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iLUGDEwPJM
% 0.14/0.36  % Computer   : n025.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:53:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 7.31/7.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.31/7.49  % Solved by: fo/fo7.sh
% 7.31/7.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.31/7.49  % done 4151 iterations in 7.019s
% 7.31/7.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.31/7.49  % SZS output start Refutation
% 7.31/7.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.31/7.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 7.31/7.49  thf(sk_B_type, type, sk_B: $i).
% 7.31/7.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.31/7.49  thf(sk_C_2_type, type, sk_C_2: $i).
% 7.31/7.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.31/7.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 7.31/7.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.31/7.49  thf(sk_E_type, type, sk_E: $i > $i).
% 7.31/7.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.31/7.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.31/7.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.31/7.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 7.31/7.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.31/7.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.31/7.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 7.31/7.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 7.31/7.49  thf(sk_A_type, type, sk_A: $i).
% 7.31/7.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.31/7.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.31/7.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 7.31/7.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.31/7.49  thf(t2_tarski, axiom,
% 7.31/7.49    (![A:$i,B:$i]:
% 7.31/7.49     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 7.31/7.49       ( ( A ) = ( B ) ) ))).
% 7.31/7.49  thf('0', plain,
% 7.31/7.49      (![X4 : $i, X5 : $i]:
% 7.31/7.49         (((X5) = (X4))
% 7.31/7.49          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 7.31/7.49          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 7.31/7.49      inference('cnf', [status(esa)], [t2_tarski])).
% 7.31/7.49  thf(t16_funct_2, conjecture,
% 7.31/7.49    (![A:$i,B:$i,C:$i]:
% 7.31/7.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.31/7.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.31/7.49       ( ( ![D:$i]:
% 7.31/7.49           ( ~( ( r2_hidden @ D @ B ) & 
% 7.31/7.49                ( ![E:$i]:
% 7.31/7.49                  ( ~( ( r2_hidden @ E @ A ) & 
% 7.31/7.49                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 7.31/7.49         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 7.31/7.49  thf(zf_stmt_0, negated_conjecture,
% 7.31/7.49    (~( ![A:$i,B:$i,C:$i]:
% 7.31/7.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.31/7.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.31/7.49          ( ( ![D:$i]:
% 7.31/7.49              ( ~( ( r2_hidden @ D @ B ) & 
% 7.31/7.49                   ( ![E:$i]:
% 7.31/7.49                     ( ~( ( r2_hidden @ E @ A ) & 
% 7.31/7.49                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 7.31/7.49            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 7.31/7.49    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 7.31/7.49  thf('1', plain,
% 7.31/7.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.49  thf(dt_k2_relset_1, axiom,
% 7.31/7.49    (![A:$i,B:$i,C:$i]:
% 7.31/7.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.31/7.49       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 7.31/7.49  thf('2', plain,
% 7.31/7.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 7.31/7.49         ((m1_subset_1 @ (k2_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 7.31/7.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 7.31/7.49      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 7.31/7.49  thf('3', plain,
% 7.31/7.49      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 7.31/7.49        (k1_zfmisc_1 @ sk_B))),
% 7.31/7.49      inference('sup-', [status(thm)], ['1', '2'])).
% 7.31/7.49  thf('4', plain,
% 7.31/7.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.49  thf(redefinition_k2_relset_1, axiom,
% 7.31/7.49    (![A:$i,B:$i,C:$i]:
% 7.31/7.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.31/7.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 7.31/7.49  thf('5', plain,
% 7.31/7.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 7.31/7.49         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 7.31/7.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 7.31/7.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 7.31/7.49  thf('6', plain,
% 7.31/7.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 7.31/7.49      inference('sup-', [status(thm)], ['4', '5'])).
% 7.31/7.49  thf('7', plain,
% 7.31/7.49      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 7.31/7.49      inference('demod', [status(thm)], ['3', '6'])).
% 7.31/7.49  thf(t3_subset, axiom,
% 7.31/7.49    (![A:$i,B:$i]:
% 7.31/7.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.31/7.49  thf('8', plain,
% 7.31/7.49      (![X7 : $i, X8 : $i]:
% 7.31/7.49         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 7.31/7.49      inference('cnf', [status(esa)], [t3_subset])).
% 7.31/7.49  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 7.31/7.49      inference('sup-', [status(thm)], ['7', '8'])).
% 7.31/7.49  thf(d3_tarski, axiom,
% 7.31/7.49    (![A:$i,B:$i]:
% 7.31/7.49     ( ( r1_tarski @ A @ B ) <=>
% 7.31/7.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.31/7.49  thf('10', plain,
% 7.31/7.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.31/7.49         (~ (r2_hidden @ X0 @ X1)
% 7.31/7.49          | (r2_hidden @ X0 @ X2)
% 7.31/7.49          | ~ (r1_tarski @ X1 @ X2))),
% 7.31/7.49      inference('cnf', [status(esa)], [d3_tarski])).
% 7.31/7.49  thf('11', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['9', '10'])).
% 7.31/7.49  thf('12', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ X0) @ X0)
% 7.31/7.49          | ((X0) = (k2_relat_1 @ sk_C_2))
% 7.31/7.49          | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ X0) @ sk_B))),
% 7.31/7.49      inference('sup-', [status(thm)], ['0', '11'])).
% 7.31/7.49  thf('13', plain,
% 7.31/7.49      ((((sk_B) = (k2_relat_1 @ sk_C_2))
% 7.31/7.49        | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B))),
% 7.31/7.49      inference('eq_fact', [status(thm)], ['12'])).
% 7.31/7.49  thf('14', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.49  thf('15', plain,
% 7.31/7.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 7.31/7.49      inference('sup-', [status(thm)], ['4', '5'])).
% 7.31/7.49  thf('16', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 7.31/7.49      inference('demod', [status(thm)], ['14', '15'])).
% 7.31/7.49  thf('17', plain,
% 7.31/7.49      ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)),
% 7.31/7.49      inference('simplify_reflect-', [status(thm)], ['13', '16'])).
% 7.31/7.49  thf('18', plain,
% 7.31/7.49      (![X1 : $i, X3 : $i]:
% 7.31/7.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.31/7.49      inference('cnf', [status(esa)], [d3_tarski])).
% 7.31/7.49  thf('19', plain,
% 7.31/7.49      (![X34 : $i]:
% 7.31/7.49         (~ (r2_hidden @ X34 @ sk_B)
% 7.31/7.49          | ((X34) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X34))))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.49  thf('20', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         ((r1_tarski @ sk_B @ X0)
% 7.31/7.49          | ((sk_C @ X0 @ sk_B)
% 7.31/7.49              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 7.31/7.49      inference('sup-', [status(thm)], ['18', '19'])).
% 7.31/7.49  thf('21', plain,
% 7.31/7.49      (![X1 : $i, X3 : $i]:
% 7.31/7.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.31/7.49      inference('cnf', [status(esa)], [d3_tarski])).
% 7.31/7.49  thf('22', plain,
% 7.31/7.49      (![X34 : $i]:
% 7.31/7.49         (~ (r2_hidden @ X34 @ sk_B) | (r2_hidden @ (sk_E @ X34) @ sk_A))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.49  thf('23', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         ((r1_tarski @ sk_B @ X0)
% 7.31/7.49          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 7.31/7.49      inference('sup-', [status(thm)], ['21', '22'])).
% 7.31/7.49  thf(d1_funct_2, axiom,
% 7.31/7.49    (![A:$i,B:$i,C:$i]:
% 7.31/7.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.31/7.49       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.31/7.49           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 7.31/7.49             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 7.31/7.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.31/7.49           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 7.31/7.49             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 7.31/7.49  thf(zf_stmt_1, axiom,
% 7.31/7.49    (![B:$i,A:$i]:
% 7.31/7.49     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.31/7.49       ( zip_tseitin_0 @ B @ A ) ))).
% 7.31/7.49  thf('24', plain,
% 7.31/7.49      (![X26 : $i, X27 : $i]:
% 7.31/7.49         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.31/7.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 7.31/7.49  thf('25', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 7.31/7.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.31/7.49  thf('26', plain,
% 7.31/7.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.31/7.49         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 7.31/7.49      inference('sup+', [status(thm)], ['24', '25'])).
% 7.31/7.49  thf('27', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 7.31/7.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.31/7.49  thf('28', plain,
% 7.31/7.49      (![X4 : $i, X5 : $i]:
% 7.31/7.49         (((X5) = (X4))
% 7.31/7.49          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 7.31/7.49          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 7.31/7.49      inference('cnf', [status(esa)], [t2_tarski])).
% 7.31/7.49  thf(t7_ordinal1, axiom,
% 7.31/7.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.31/7.49  thf('29', plain,
% 7.31/7.49      (![X12 : $i, X13 : $i]:
% 7.31/7.49         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 7.31/7.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 7.31/7.49  thf('30', plain,
% 7.31/7.49      (![X0 : $i, X1 : $i]:
% 7.31/7.49         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 7.31/7.49          | ((X0) = (X1))
% 7.31/7.49          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X1 @ X0)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['28', '29'])).
% 7.31/7.49  thf('31', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         (((k1_xboole_0) = (X0))
% 7.31/7.49          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 7.31/7.49      inference('sup-', [status(thm)], ['27', '30'])).
% 7.31/7.49  thf('32', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['9', '10'])).
% 7.31/7.49  thf('33', plain,
% 7.31/7.49      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_2))
% 7.31/7.49        | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ k1_xboole_0) @ sk_B))),
% 7.31/7.49      inference('sup-', [status(thm)], ['31', '32'])).
% 7.31/7.49  thf('34', plain,
% 7.31/7.49      (![X12 : $i, X13 : $i]:
% 7.31/7.49         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 7.31/7.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 7.31/7.49  thf('35', plain,
% 7.31/7.49      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_2))
% 7.31/7.49        | ~ (r1_tarski @ sk_B @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ k1_xboole_0)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['33', '34'])).
% 7.31/7.49  thf('36', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         ((zip_tseitin_0 @ sk_B @ X0) | ((k1_xboole_0) = (k2_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['26', '35'])).
% 7.31/7.49  thf('37', plain,
% 7.31/7.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.49  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 7.31/7.49  thf(zf_stmt_3, axiom,
% 7.31/7.49    (![C:$i,B:$i,A:$i]:
% 7.31/7.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 7.31/7.49       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 7.31/7.49  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 7.31/7.49  thf(zf_stmt_5, axiom,
% 7.31/7.49    (![A:$i,B:$i,C:$i]:
% 7.31/7.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.31/7.49       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 7.31/7.49         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.31/7.49           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 7.31/7.49             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 7.31/7.49  thf('38', plain,
% 7.31/7.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.31/7.49         (~ (zip_tseitin_0 @ X31 @ X32)
% 7.31/7.49          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 7.31/7.49          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.31/7.49  thf('39', plain,
% 7.31/7.49      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.31/7.49        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 7.31/7.49      inference('sup-', [status(thm)], ['37', '38'])).
% 7.31/7.49  thf('40', plain,
% 7.31/7.49      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_2))
% 7.31/7.49        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 7.31/7.49      inference('sup-', [status(thm)], ['36', '39'])).
% 7.31/7.49  thf('41', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.49  thf('42', plain,
% 7.31/7.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 7.31/7.49         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 7.31/7.49          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 7.31/7.49          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 7.31/7.49  thf('43', plain,
% 7.31/7.49      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.31/7.49        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['41', '42'])).
% 7.31/7.49  thf('44', plain,
% 7.31/7.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.49  thf(redefinition_k1_relset_1, axiom,
% 7.31/7.49    (![A:$i,B:$i,C:$i]:
% 7.31/7.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.31/7.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 7.31/7.49  thf('45', plain,
% 7.31/7.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 7.31/7.49         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 7.31/7.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 7.31/7.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.31/7.49  thf('46', plain,
% 7.31/7.49      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 7.31/7.49      inference('sup-', [status(thm)], ['44', '45'])).
% 7.31/7.49  thf('47', plain,
% 7.31/7.49      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.31/7.49        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('demod', [status(thm)], ['43', '46'])).
% 7.31/7.49  thf('48', plain,
% 7.31/7.49      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_2))
% 7.31/7.49        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['40', '47'])).
% 7.31/7.49  thf('49', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 7.31/7.49      inference('demod', [status(thm)], ['14', '15'])).
% 7.31/7.49  thf('50', plain,
% 7.31/7.49      ((((k1_xboole_0) != (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['48', '49'])).
% 7.31/7.49  thf('51', plain,
% 7.31/7.49      (![X26 : $i, X27 : $i]:
% 7.31/7.49         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.31/7.49  thf('52', plain,
% 7.31/7.49      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.31/7.49        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 7.31/7.49      inference('sup-', [status(thm)], ['37', '38'])).
% 7.31/7.49  thf('53', plain,
% 7.31/7.49      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 7.31/7.49      inference('sup-', [status(thm)], ['51', '52'])).
% 7.31/7.49  thf('54', plain,
% 7.31/7.49      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 7.31/7.49        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('demod', [status(thm)], ['43', '46'])).
% 7.31/7.49  thf('55', plain,
% 7.31/7.49      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['53', '54'])).
% 7.31/7.49  thf('56', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 7.31/7.49      inference('clc', [status(thm)], ['50', '55'])).
% 7.31/7.49  thf(t12_funct_1, axiom,
% 7.31/7.49    (![A:$i,B:$i]:
% 7.31/7.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 7.31/7.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 7.31/7.49         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 7.31/7.49  thf('57', plain,
% 7.31/7.49      (![X10 : $i, X11 : $i]:
% 7.31/7.49         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 7.31/7.49          | (r2_hidden @ (k1_funct_1 @ X11 @ X10) @ (k2_relat_1 @ X11))
% 7.31/7.49          | ~ (v1_funct_1 @ X11)
% 7.31/7.49          | ~ (v1_relat_1 @ X11))),
% 7.31/7.49      inference('cnf', [status(esa)], [t12_funct_1])).
% 7.31/7.49  thf('58', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         (~ (r2_hidden @ X0 @ sk_A)
% 7.31/7.49          | ~ (v1_relat_1 @ sk_C_2)
% 7.31/7.49          | ~ (v1_funct_1 @ sk_C_2)
% 7.31/7.49          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['56', '57'])).
% 7.31/7.49  thf('59', plain,
% 7.31/7.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.49  thf(cc1_relset_1, axiom,
% 7.31/7.49    (![A:$i,B:$i,C:$i]:
% 7.31/7.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.31/7.49       ( v1_relat_1 @ C ) ))).
% 7.31/7.49  thf('60', plain,
% 7.31/7.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 7.31/7.49         ((v1_relat_1 @ X14)
% 7.31/7.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 7.31/7.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.31/7.49  thf('61', plain, ((v1_relat_1 @ sk_C_2)),
% 7.31/7.49      inference('sup-', [status(thm)], ['59', '60'])).
% 7.31/7.49  thf('62', plain, ((v1_funct_1 @ sk_C_2)),
% 7.31/7.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.31/7.49  thf('63', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         (~ (r2_hidden @ X0 @ sk_A)
% 7.31/7.49          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('demod', [status(thm)], ['58', '61', '62'])).
% 7.31/7.49  thf('64', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         ((r1_tarski @ sk_B @ X0)
% 7.31/7.49          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 7.31/7.49             (k2_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['23', '63'])).
% 7.31/7.49  thf('65', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 7.31/7.49          | (r1_tarski @ sk_B @ X0)
% 7.31/7.49          | (r1_tarski @ sk_B @ X0))),
% 7.31/7.49      inference('sup+', [status(thm)], ['20', '64'])).
% 7.31/7.49  thf('66', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         ((r1_tarski @ sk_B @ X0)
% 7.31/7.49          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('simplify', [status(thm)], ['65'])).
% 7.31/7.49  thf('67', plain,
% 7.31/7.49      (![X1 : $i, X3 : $i]:
% 7.31/7.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.31/7.49      inference('cnf', [status(esa)], [d3_tarski])).
% 7.31/7.49  thf('68', plain,
% 7.31/7.49      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 7.31/7.49        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['66', '67'])).
% 7.31/7.49  thf('69', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 7.31/7.49      inference('simplify', [status(thm)], ['68'])).
% 7.31/7.49  thf('70', plain,
% 7.31/7.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.31/7.49         (~ (r2_hidden @ X0 @ X1)
% 7.31/7.49          | (r2_hidden @ X0 @ X2)
% 7.31/7.49          | ~ (r1_tarski @ X1 @ X2))),
% 7.31/7.49      inference('cnf', [status(esa)], [d3_tarski])).
% 7.31/7.49  thf('71', plain,
% 7.31/7.49      (![X0 : $i]:
% 7.31/7.49         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)) | ~ (r2_hidden @ X0 @ sk_B))),
% 7.31/7.49      inference('sup-', [status(thm)], ['69', '70'])).
% 7.31/7.49  thf('72', plain,
% 7.31/7.49      ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ 
% 7.31/7.49        (k2_relat_1 @ sk_C_2))),
% 7.31/7.49      inference('sup-', [status(thm)], ['17', '71'])).
% 7.31/7.49  thf('73', plain,
% 7.31/7.49      (![X4 : $i, X5 : $i]:
% 7.31/7.49         (((X5) = (X4))
% 7.31/7.49          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 7.31/7.49          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 7.31/7.49      inference('cnf', [status(esa)], [t2_tarski])).
% 7.31/7.49  thf('74', plain,
% 7.31/7.49      ((~ (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)
% 7.31/7.49        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 7.31/7.49      inference('sup-', [status(thm)], ['72', '73'])).
% 7.31/7.49  thf('75', plain,
% 7.31/7.49      ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)),
% 7.31/7.49      inference('simplify_reflect-', [status(thm)], ['13', '16'])).
% 7.31/7.49  thf('76', plain, (((sk_B) = (k2_relat_1 @ sk_C_2))),
% 7.31/7.49      inference('demod', [status(thm)], ['74', '75'])).
% 7.31/7.49  thf('77', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 7.31/7.49      inference('demod', [status(thm)], ['14', '15'])).
% 7.31/7.49  thf('78', plain, ($false),
% 7.31/7.49      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 7.31/7.49  
% 7.31/7.49  % SZS output end Refutation
% 7.31/7.49  
% 7.31/7.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
