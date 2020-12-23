%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lVdEUMeUOU

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:09 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  279 (3008 expanded)
%              Number of leaves         :   50 ( 916 expanded)
%              Depth                    :   30
%              Number of atoms          : 1832 (26882 expanded)
%              Number of equality atoms :  164 (2012 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) @ X23 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) @ X23 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('19',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('22',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('41',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','43'])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('45',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42
       != ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X41 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,(
    ! [X40: $i] :
      ( zip_tseitin_0 @ X40 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['47','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','55'])).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('61',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['59','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['57'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('81',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('82',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('85',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('86',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('90',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['88','93'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('95',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X38 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['91','92'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','98'])).

thf('100',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['57'])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['57'])).

thf('103',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['78','101','102'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['75','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('106',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('107',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) @ X23 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('109',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('111',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('112',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('113',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('117',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['110','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['109','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('121',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('122',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('125',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('128',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('130',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('132',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['129','136'])).

thf('138',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['108','139'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('141',plain,(
    ! [X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('147',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('148',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('150',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['12','22'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['148','153'])).

thf('155',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k6_relat_1 @ sk_B_1 )
      = ( k2_zfmisc_1 @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['145','154'])).

thf('156',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('157',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k6_relat_1 @ sk_B_1 )
      = ( k2_zfmisc_1 @ sk_B_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['108','139'])).

thf('159',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B_1 ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('161',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('164',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['47','53'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('167',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['163'])).

thf('168',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('169',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('171',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('173',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('174',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['166','174'])).

thf('176',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['163'])).

thf('177',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['57'])).

thf('178',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['175','178'])).

thf('180',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['165','179'])).

thf('181',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('182',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('183',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('185',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['163'])).

thf('186',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['57'])).

thf('187',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['184','187'])).

thf('189',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['183','188'])).

thf('190',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['57'])).

thf('191',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['163'])).

thf('192',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['78','180','189','190','191'])).

thf('193',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['164','192'])).

thf('194',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['162','193'])).

thf('195',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['107','194'])).

thf('196',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','98'])).

thf('197',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('198',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('200',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('202',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','98'])).

thf('203',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('204',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','98'])).

thf('206',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('207',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['162','193'])).

thf('209',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42
       != ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['57'])).

thf('214',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['78','101','102'])).

thf('215',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['212','215'])).

thf('217',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['204','216'])).

thf('218',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['201','217'])).

thf('219',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('220',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['12','22'])).

thf('221',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['201','217'])).

thf('222',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('223',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['200','218','219','220','221','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','43'])).

thf('225',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['195','223','224'])).

thf('226',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('227',plain,(
    $false ),
    inference(demod,[status(thm)],['104','225','226'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lVdEUMeUOU
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.83  % Solved by: fo/fo7.sh
% 1.65/1.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.83  % done 2115 iterations in 1.368s
% 1.65/1.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.83  % SZS output start Refutation
% 1.65/1.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.83  thf(sk_B_type, type, sk_B: $i > $i).
% 1.65/1.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.65/1.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.83  thf(sk_D_type, type, sk_D: $i).
% 1.65/1.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.65/1.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.65/1.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.65/1.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.65/1.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.65/1.83  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.65/1.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.65/1.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.65/1.83  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.65/1.83  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.83  thf(t7_xboole_0, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.65/1.83          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.65/1.83  thf('0', plain,
% 1.65/1.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.65/1.83      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.65/1.83  thf(d10_xboole_0, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.65/1.83  thf('1', plain,
% 1.65/1.83      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 1.65/1.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.83  thf('2', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.65/1.83      inference('simplify', [status(thm)], ['1'])).
% 1.65/1.83  thf(t3_subset, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.65/1.83  thf('3', plain,
% 1.65/1.83      (![X10 : $i, X12 : $i]:
% 1.65/1.83         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.65/1.83      inference('cnf', [status(esa)], [t3_subset])).
% 1.65/1.83  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['2', '3'])).
% 1.65/1.83  thf(t5_subset, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.65/1.83          ( v1_xboole_0 @ C ) ) ))).
% 1.65/1.83  thf('5', plain,
% 1.65/1.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X13 @ X14)
% 1.65/1.83          | ~ (v1_xboole_0 @ X15)
% 1.65/1.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t5_subset])).
% 1.65/1.83  thf('6', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['4', '5'])).
% 1.65/1.83  thf('7', plain,
% 1.65/1.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['0', '6'])).
% 1.65/1.83  thf('8', plain,
% 1.65/1.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['0', '6'])).
% 1.65/1.83  thf(t113_zfmisc_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.65/1.83       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.65/1.83  thf('9', plain,
% 1.65/1.83      (![X8 : $i, X9 : $i]:
% 1.65/1.83         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.65/1.83  thf('10', plain,
% 1.65/1.83      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['9'])).
% 1.65/1.83  thf(t194_relat_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 1.65/1.83  thf('11', plain,
% 1.65/1.83      (![X22 : $i, X23 : $i]:
% 1.65/1.83         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X22 @ X23)) @ X23)),
% 1.65/1.83      inference('cnf', [status(esa)], [t194_relat_1])).
% 1.65/1.83  thf('12', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 1.65/1.83      inference('sup+', [status(thm)], ['10', '11'])).
% 1.65/1.83  thf('13', plain,
% 1.65/1.83      (![X22 : $i, X23 : $i]:
% 1.65/1.83         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X22 @ X23)) @ X23)),
% 1.65/1.83      inference('cnf', [status(esa)], [t194_relat_1])).
% 1.65/1.83  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.65/1.83  thf('14', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 1.65/1.83      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.65/1.83  thf(t69_xboole_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.65/1.83       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.65/1.83  thf('15', plain,
% 1.65/1.83      (![X5 : $i, X6 : $i]:
% 1.65/1.83         (~ (r1_xboole_0 @ X5 @ X6)
% 1.65/1.83          | ~ (r1_tarski @ X5 @ X6)
% 1.65/1.83          | (v1_xboole_0 @ X5))),
% 1.65/1.83      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.65/1.83  thf('16', plain,
% 1.65/1.83      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['14', '15'])).
% 1.65/1.83  thf('17', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (v1_xboole_0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['13', '16'])).
% 1.65/1.83  thf('18', plain,
% 1.65/1.83      (![X8 : $i, X9 : $i]:
% 1.65/1.83         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.65/1.83  thf('19', plain,
% 1.65/1.83      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['18'])).
% 1.65/1.83  thf('20', plain, ((v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))),
% 1.65/1.83      inference('demod', [status(thm)], ['17', '19'])).
% 1.65/1.83  thf('21', plain,
% 1.65/1.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['0', '6'])).
% 1.65/1.83  thf('22', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['20', '21'])).
% 1.65/1.83  thf('23', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.65/1.83      inference('demod', [status(thm)], ['12', '22'])).
% 1.65/1.83  thf('24', plain,
% 1.65/1.83      (![X10 : $i, X12 : $i]:
% 1.65/1.83         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.65/1.83      inference('cnf', [status(esa)], [t3_subset])).
% 1.65/1.83  thf('25', plain,
% 1.65/1.83      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['23', '24'])).
% 1.65/1.83  thf(redefinition_k1_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.65/1.83  thf('26', plain,
% 1.65/1.83      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.65/1.83         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.65/1.83          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.65/1.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.65/1.83  thf('27', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['25', '26'])).
% 1.65/1.83  thf('28', plain,
% 1.65/1.83      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['23', '24'])).
% 1.65/1.83  thf(cc2_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.65/1.83  thf('29', plain,
% 1.65/1.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.65/1.83         ((v4_relat_1 @ X27 @ X28)
% 1.65/1.83          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.65/1.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.83  thf('30', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 1.65/1.83      inference('sup-', [status(thm)], ['28', '29'])).
% 1.65/1.83  thf(d18_relat_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( v1_relat_1 @ B ) =>
% 1.65/1.83       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.65/1.83  thf('31', plain,
% 1.65/1.83      (![X18 : $i, X19 : $i]:
% 1.65/1.83         (~ (v4_relat_1 @ X18 @ X19)
% 1.65/1.83          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.65/1.83          | ~ (v1_relat_1 @ X18))),
% 1.65/1.83      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.83  thf('32', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.83          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.83  thf('33', plain,
% 1.65/1.83      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['9'])).
% 1.65/1.83  thf(fc6_relat_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.65/1.83  thf('34', plain,
% 1.65/1.83      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.83  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.65/1.83      inference('sup+', [status(thm)], ['33', '34'])).
% 1.65/1.83  thf('36', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.65/1.83      inference('demod', [status(thm)], ['32', '35'])).
% 1.65/1.83  thf('37', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 1.65/1.83      inference('sup+', [status(thm)], ['10', '11'])).
% 1.65/1.83  thf('38', plain,
% 1.65/1.83      (![X1 : $i, X3 : $i]:
% 1.65/1.83         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.65/1.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.83  thf('39', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (r1_tarski @ X0 @ (k2_relat_1 @ k1_xboole_0))
% 1.65/1.83          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['37', '38'])).
% 1.65/1.83  thf('40', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['20', '21'])).
% 1.65/1.83  thf('41', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['20', '21'])).
% 1.65/1.83  thf('42', plain,
% 1.65/1.83      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.65/1.83      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.65/1.83  thf('43', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['36', '42'])).
% 1.65/1.83  thf('44', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('demod', [status(thm)], ['27', '43'])).
% 1.65/1.83  thf(d1_funct_2, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.65/1.83           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.65/1.83             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.65/1.83         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.83           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.65/1.83             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_0, axiom,
% 1.65/1.83    (![C:$i,B:$i,A:$i]:
% 1.65/1.83     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.65/1.83       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.65/1.83  thf('45', plain,
% 1.65/1.83      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.65/1.83         (((X42) != (k1_relset_1 @ X42 @ X43 @ X44))
% 1.65/1.83          | (v1_funct_2 @ X44 @ X42 @ X43)
% 1.65/1.83          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('46', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (((X1) != (k1_xboole_0))
% 1.65/1.83          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.65/1.83          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['44', '45'])).
% 1.65/1.83  thf('47', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.65/1.83          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['46'])).
% 1.65/1.83  thf(zf_stmt_1, axiom,
% 1.65/1.83    (![B:$i,A:$i]:
% 1.65/1.83     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.83       ( zip_tseitin_0 @ B @ A ) ))).
% 1.65/1.83  thf('48', plain,
% 1.65/1.83      (![X40 : $i, X41 : $i]:
% 1.65/1.83         ((zip_tseitin_0 @ X40 @ X41) | ((X41) != (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.83  thf('49', plain, (![X40 : $i]: (zip_tseitin_0 @ X40 @ k1_xboole_0)),
% 1.65/1.83      inference('simplify', [status(thm)], ['48'])).
% 1.65/1.83  thf('50', plain,
% 1.65/1.83      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['23', '24'])).
% 1.65/1.83  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.65/1.83  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.65/1.83  thf(zf_stmt_4, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.65/1.83         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.65/1.83           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.65/1.83             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.65/1.83  thf('51', plain,
% 1.65/1.83      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.65/1.83         (~ (zip_tseitin_0 @ X45 @ X46)
% 1.65/1.83          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 1.65/1.83          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.65/1.83  thf('52', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['50', '51'])).
% 1.65/1.83  thf('53', plain,
% 1.65/1.83      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.65/1.83      inference('sup-', [status(thm)], ['49', '52'])).
% 1.65/1.83  thf('54', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.65/1.83      inference('demod', [status(thm)], ['47', '53'])).
% 1.65/1.83  thf('55', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['8', '54'])).
% 1.65/1.83  thf('56', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((v1_funct_2 @ X2 @ X0 @ X1)
% 1.65/1.83          | ~ (v1_xboole_0 @ X0)
% 1.65/1.83          | ~ (v1_xboole_0 @ X2))),
% 1.65/1.83      inference('sup+', [status(thm)], ['7', '55'])).
% 1.65/1.83  thf(t8_funct_2, conjecture,
% 1.65/1.83    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.83     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.65/1.83         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.83       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.65/1.83         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.65/1.83           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.65/1.83             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.65/1.83  thf(zf_stmt_5, negated_conjecture,
% 1.65/1.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.83        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.65/1.83            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.83          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.65/1.83            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.65/1.83              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.65/1.83                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.65/1.83    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 1.65/1.83  thf('57', plain,
% 1.65/1.83      ((~ (v1_funct_1 @ sk_D)
% 1.65/1.83        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 1.65/1.83        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('58', plain,
% 1.65/1.83      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.65/1.83         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.65/1.83      inference('split', [status(esa)], ['57'])).
% 1.65/1.83  thf('59', plain,
% 1.65/1.83      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 1.65/1.83         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['56', '58'])).
% 1.65/1.83  thf('60', plain,
% 1.65/1.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['0', '6'])).
% 1.65/1.83  thf('61', plain,
% 1.65/1.83      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['9'])).
% 1.65/1.83  thf('62', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['60', '61'])).
% 1.65/1.83  thf('63', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('64', plain,
% 1.65/1.83      (![X10 : $i, X11 : $i]:
% 1.65/1.83         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t3_subset])).
% 1.65/1.83  thf('65', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.83  thf('66', plain,
% 1.65/1.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['0', '6'])).
% 1.65/1.83  thf('67', plain,
% 1.65/1.83      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['14', '15'])).
% 1.65/1.83  thf('68', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (r1_tarski @ X1 @ X0) | ~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ X1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['66', '67'])).
% 1.65/1.83  thf('69', plain,
% 1.65/1.83      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['65', '68'])).
% 1.65/1.83  thf('70', plain,
% 1.65/1.83      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.83        | ~ (v1_xboole_0 @ sk_A)
% 1.65/1.83        | (v1_xboole_0 @ sk_D))),
% 1.65/1.83      inference('sup-', [status(thm)], ['62', '69'])).
% 1.65/1.83  thf('71', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.65/1.83      inference('simplify', [status(thm)], ['1'])).
% 1.65/1.83  thf('72', plain,
% 1.65/1.83      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['14', '15'])).
% 1.65/1.83  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.83      inference('sup-', [status(thm)], ['71', '72'])).
% 1.65/1.83  thf('74', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 1.65/1.83      inference('demod', [status(thm)], ['70', '73'])).
% 1.65/1.83  thf('75', plain,
% 1.65/1.83      ((~ (v1_xboole_0 @ sk_A)) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.65/1.83      inference('clc', [status(thm)], ['59', '74'])).
% 1.65/1.83  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('77', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.65/1.83      inference('split', [status(esa)], ['57'])).
% 1.65/1.83  thf('78', plain, (((v1_funct_1 @ sk_D))),
% 1.65/1.83      inference('sup-', [status(thm)], ['76', '77'])).
% 1.65/1.83  thf('79', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('80', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf(redefinition_k2_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.83       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.65/1.83  thf('81', plain,
% 1.65/1.83      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.65/1.83         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 1.65/1.83          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.65/1.83      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.83  thf('82', plain,
% 1.65/1.83      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.65/1.83      inference('sup-', [status(thm)], ['80', '81'])).
% 1.65/1.83  thf('83', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 1.65/1.83      inference('demod', [status(thm)], ['79', '82'])).
% 1.65/1.83  thf('84', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('85', plain,
% 1.65/1.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.65/1.83         ((v4_relat_1 @ X27 @ X28)
% 1.65/1.83          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.65/1.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.83  thf('86', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.65/1.83      inference('sup-', [status(thm)], ['84', '85'])).
% 1.65/1.83  thf('87', plain,
% 1.65/1.83      (![X18 : $i, X19 : $i]:
% 1.65/1.83         (~ (v4_relat_1 @ X18 @ X19)
% 1.65/1.83          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.65/1.83          | ~ (v1_relat_1 @ X18))),
% 1.65/1.83      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.83  thf('88', plain,
% 1.65/1.83      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['86', '87'])).
% 1.65/1.83  thf('89', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf(cc2_relat_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( v1_relat_1 @ A ) =>
% 1.65/1.83       ( ![B:$i]:
% 1.65/1.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.65/1.83  thf('90', plain,
% 1.65/1.83      (![X16 : $i, X17 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.65/1.83          | (v1_relat_1 @ X16)
% 1.65/1.83          | ~ (v1_relat_1 @ X17))),
% 1.65/1.83      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.65/1.83  thf('91', plain,
% 1.65/1.83      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 1.65/1.83      inference('sup-', [status(thm)], ['89', '90'])).
% 1.65/1.83  thf('92', plain,
% 1.65/1.83      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.83  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.83      inference('demod', [status(thm)], ['91', '92'])).
% 1.65/1.83  thf('94', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 1.65/1.83      inference('demod', [status(thm)], ['88', '93'])).
% 1.65/1.83  thf(t11_relset_1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( v1_relat_1 @ C ) =>
% 1.65/1.83       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.65/1.83           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.65/1.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.65/1.83  thf('95', plain,
% 1.65/1.83      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.65/1.83         (~ (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 1.65/1.83          | ~ (r1_tarski @ (k2_relat_1 @ X36) @ X38)
% 1.65/1.83          | (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.65/1.83          | ~ (v1_relat_1 @ X36))),
% 1.65/1.83      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.65/1.83  thf('96', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v1_relat_1 @ sk_D)
% 1.65/1.83          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.83          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['94', '95'])).
% 1.65/1.83  thf('97', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.83      inference('demod', [status(thm)], ['91', '92'])).
% 1.65/1.83  thf('98', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.83          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.65/1.83      inference('demod', [status(thm)], ['96', '97'])).
% 1.65/1.83  thf('99', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['83', '98'])).
% 1.65/1.83  thf('100', plain,
% 1.65/1.83      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.65/1.83      inference('split', [status(esa)], ['57'])).
% 1.65/1.83  thf('101', plain,
% 1.65/1.83      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['99', '100'])).
% 1.65/1.83  thf('102', plain,
% 1.65/1.83      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 1.65/1.83       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.65/1.83       ~ ((v1_funct_1 @ sk_D))),
% 1.65/1.83      inference('split', [status(esa)], ['57'])).
% 1.65/1.83  thf('103', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.65/1.83      inference('sat_resolution*', [status(thm)], ['78', '101', '102'])).
% 1.65/1.83  thf('104', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.65/1.83      inference('simpl_trail', [status(thm)], ['75', '103'])).
% 1.65/1.83  thf('105', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('106', plain,
% 1.65/1.83      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.65/1.83         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.65/1.83          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.65/1.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.65/1.83  thf('107', plain,
% 1.65/1.83      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.65/1.83      inference('sup-', [status(thm)], ['105', '106'])).
% 1.65/1.83  thf('108', plain,
% 1.65/1.83      (![X22 : $i, X23 : $i]:
% 1.65/1.83         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X22 @ X23)) @ X23)),
% 1.65/1.83      inference('cnf', [status(esa)], [t194_relat_1])).
% 1.65/1.83  thf('109', plain,
% 1.65/1.83      (![X40 : $i, X41 : $i]:
% 1.65/1.83         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.83  thf('110', plain,
% 1.65/1.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.65/1.83      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.65/1.83  thf('111', plain,
% 1.65/1.83      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['18'])).
% 1.65/1.83  thf(t29_relset_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( m1_subset_1 @
% 1.65/1.83       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.65/1.83  thf('112', plain,
% 1.65/1.83      (![X39 : $i]:
% 1.65/1.83         (m1_subset_1 @ (k6_relat_1 @ X39) @ 
% 1.65/1.83          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.65/1.83  thf('113', plain,
% 1.65/1.83      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['111', '112'])).
% 1.65/1.83  thf('114', plain,
% 1.65/1.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X13 @ X14)
% 1.65/1.83          | ~ (v1_xboole_0 @ X15)
% 1.65/1.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t5_subset])).
% 1.65/1.83  thf('115', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.83          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['113', '114'])).
% 1.65/1.83  thf('116', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.83      inference('sup-', [status(thm)], ['71', '72'])).
% 1.65/1.83  thf('117', plain,
% 1.65/1.83      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 1.65/1.83      inference('demod', [status(thm)], ['115', '116'])).
% 1.65/1.83  thf('118', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['110', '117'])).
% 1.65/1.83  thf('119', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (((k6_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 1.65/1.83      inference('sup+', [status(thm)], ['109', '118'])).
% 1.65/1.83  thf('120', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('121', plain,
% 1.65/1.83      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.65/1.83         (~ (zip_tseitin_0 @ X45 @ X46)
% 1.65/1.83          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 1.65/1.83          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.65/1.83  thf('122', plain,
% 1.65/1.83      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.65/1.83        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['120', '121'])).
% 1.65/1.83  thf('123', plain,
% 1.65/1.83      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0))
% 1.65/1.83        | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['119', '122'])).
% 1.65/1.83  thf('124', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('125', plain,
% 1.65/1.83      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.65/1.83         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 1.65/1.83          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 1.65/1.83          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('126', plain,
% 1.65/1.83      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.65/1.83        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['124', '125'])).
% 1.65/1.83  thf('127', plain,
% 1.65/1.83      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.65/1.83      inference('sup-', [status(thm)], ['105', '106'])).
% 1.65/1.83  thf('128', plain,
% 1.65/1.83      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.65/1.83        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.65/1.83      inference('demod', [status(thm)], ['126', '127'])).
% 1.65/1.83  thf('129', plain,
% 1.65/1.83      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0))
% 1.65/1.83        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['123', '128'])).
% 1.65/1.83  thf(t71_relat_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.65/1.83       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.65/1.83  thf('130', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 1.65/1.83      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.65/1.83  thf('131', plain,
% 1.65/1.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['0', '6'])).
% 1.65/1.83  thf('132', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['20', '21'])).
% 1.65/1.83  thf('133', plain,
% 1.65/1.83      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['131', '132'])).
% 1.65/1.83  thf('134', plain,
% 1.65/1.83      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.65/1.83      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.65/1.83  thf('135', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (r1_tarski @ X1 @ (k2_relat_1 @ X0))
% 1.65/1.83          | ~ (v1_xboole_0 @ X0)
% 1.65/1.83          | ((X1) = (k1_xboole_0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['133', '134'])).
% 1.65/1.83  thf('136', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (r1_tarski @ X1 @ X0)
% 1.65/1.83          | ((X1) = (k1_xboole_0))
% 1.65/1.83          | ~ (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['130', '135'])).
% 1.65/1.83  thf('137', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.83          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.65/1.83          | ((X0) = (k1_xboole_0))
% 1.65/1.83          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 1.65/1.83      inference('sup-', [status(thm)], ['129', '136'])).
% 1.65/1.83  thf('138', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.83      inference('sup-', [status(thm)], ['71', '72'])).
% 1.65/1.83  thf('139', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.65/1.83          | ((X0) = (k1_xboole_0))
% 1.65/1.83          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 1.65/1.83      inference('demod', [status(thm)], ['137', '138'])).
% 1.65/1.83  thf('140', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)) = (k1_xboole_0))
% 1.65/1.83          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['108', '139'])).
% 1.65/1.83  thf(t64_relat_1, axiom,
% 1.65/1.83    (![A:$i]:
% 1.65/1.83     ( ( v1_relat_1 @ A ) =>
% 1.65/1.83       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.65/1.83           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.83         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.65/1.83  thf('141', plain,
% 1.65/1.83      (![X24 : $i]:
% 1.65/1.83         (((k2_relat_1 @ X24) != (k1_xboole_0))
% 1.65/1.83          | ((X24) = (k1_xboole_0))
% 1.65/1.83          | ~ (v1_relat_1 @ X24))),
% 1.65/1.83      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.65/1.83  thf('142', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((k1_xboole_0) != (k1_xboole_0))
% 1.65/1.83          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.65/1.83          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1))
% 1.65/1.83          | ((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['140', '141'])).
% 1.65/1.83  thf('143', plain,
% 1.65/1.83      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.65/1.83  thf('144', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((k1_xboole_0) != (k1_xboole_0))
% 1.65/1.83          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.65/1.83          | ((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0)))),
% 1.65/1.83      inference('demod', [status(thm)], ['142', '143'])).
% 1.65/1.83  thf('145', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((k2_zfmisc_1 @ X0 @ sk_B_1) = (k1_xboole_0))
% 1.65/1.83          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.65/1.83      inference('simplify', [status(thm)], ['144'])).
% 1.65/1.83  thf('146', plain,
% 1.65/1.83      (![X39 : $i]:
% 1.65/1.83         (m1_subset_1 @ (k6_relat_1 @ X39) @ 
% 1.65/1.83          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.65/1.83  thf('147', plain,
% 1.65/1.83      (![X10 : $i, X11 : $i]:
% 1.65/1.83         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t3_subset])).
% 1.65/1.83  thf('148', plain,
% 1.65/1.83      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['146', '147'])).
% 1.65/1.83  thf('149', plain,
% 1.65/1.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['0', '6'])).
% 1.65/1.83  thf('150', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.65/1.83      inference('demod', [status(thm)], ['12', '22'])).
% 1.65/1.83  thf('151', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['149', '150'])).
% 1.65/1.83  thf('152', plain,
% 1.65/1.83      (![X1 : $i, X3 : $i]:
% 1.65/1.83         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.65/1.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.83  thf('153', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['151', '152'])).
% 1.65/1.83  thf('154', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((k6_relat_1 @ X0) = (k2_zfmisc_1 @ X0 @ X0))
% 1.65/1.83          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['148', '153'])).
% 1.65/1.83  thf('155', plain,
% 1.65/1.83      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.83        | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.65/1.83        | ((k6_relat_1 @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_B_1)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['145', '154'])).
% 1.65/1.83  thf('156', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.83      inference('sup-', [status(thm)], ['71', '72'])).
% 1.65/1.83  thf('157', plain,
% 1.65/1.83      ((((sk_A) = (k1_relat_1 @ sk_D))
% 1.65/1.83        | ((k6_relat_1 @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_B_1)))),
% 1.65/1.83      inference('demod', [status(thm)], ['155', '156'])).
% 1.65/1.83  thf('158', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)) = (k1_xboole_0))
% 1.65/1.83          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['108', '139'])).
% 1.65/1.83  thf('159', plain,
% 1.65/1.83      ((((k2_relat_1 @ (k6_relat_1 @ sk_B_1)) = (k1_xboole_0))
% 1.65/1.83        | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.65/1.83        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['157', '158'])).
% 1.65/1.83  thf('160', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 1.65/1.83      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.65/1.83  thf('161', plain,
% 1.65/1.83      ((((sk_B_1) = (k1_xboole_0))
% 1.65/1.83        | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.65/1.83        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.65/1.83      inference('demod', [status(thm)], ['159', '160'])).
% 1.65/1.83  thf('162', plain,
% 1.65/1.83      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.65/1.83      inference('simplify', [status(thm)], ['161'])).
% 1.65/1.83  thf('163', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('164', plain,
% 1.65/1.83      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.65/1.83      inference('split', [status(esa)], ['163'])).
% 1.65/1.83  thf('165', plain,
% 1.65/1.83      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.65/1.83      inference('demod', [status(thm)], ['47', '53'])).
% 1.65/1.83  thf('166', plain,
% 1.65/1.83      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.65/1.83      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.65/1.83  thf('167', plain,
% 1.65/1.83      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('split', [status(esa)], ['163'])).
% 1.65/1.83  thf('168', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.65/1.83  thf('169', plain,
% 1.65/1.83      (((m1_subset_1 @ sk_D @ 
% 1.65/1.83         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['167', '168'])).
% 1.65/1.83  thf('170', plain,
% 1.65/1.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X13 @ X14)
% 1.65/1.83          | ~ (v1_xboole_0 @ X15)
% 1.65/1.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t5_subset])).
% 1.65/1.83  thf('171', plain,
% 1.65/1.83      ((![X0 : $i]:
% 1.65/1.83          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 1.65/1.83           | ~ (r2_hidden @ X0 @ sk_D)))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['169', '170'])).
% 1.65/1.83  thf('172', plain,
% 1.65/1.83      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['9'])).
% 1.65/1.83  thf('173', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.83      inference('sup-', [status(thm)], ['71', '72'])).
% 1.65/1.83  thf('174', plain,
% 1.65/1.83      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('demod', [status(thm)], ['171', '172', '173'])).
% 1.65/1.83  thf('175', plain,
% 1.65/1.83      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['166', '174'])).
% 1.65/1.83  thf('176', plain,
% 1.65/1.83      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('split', [status(esa)], ['163'])).
% 1.65/1.83  thf('177', plain,
% 1.65/1.83      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.65/1.83         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.65/1.83      inference('split', [status(esa)], ['57'])).
% 1.65/1.83  thf('178', plain,
% 1.65/1.83      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 1.65/1.83         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['176', '177'])).
% 1.65/1.83  thf('179', plain,
% 1.65/1.83      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 1.65/1.83         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['175', '178'])).
% 1.65/1.83  thf('180', plain,
% 1.65/1.83      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['165', '179'])).
% 1.65/1.83  thf('181', plain,
% 1.65/1.83      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['9'])).
% 1.65/1.83  thf('182', plain,
% 1.65/1.83      (((m1_subset_1 @ sk_D @ 
% 1.65/1.83         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['167', '168'])).
% 1.65/1.83  thf('183', plain,
% 1.65/1.83      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.65/1.83         <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['181', '182'])).
% 1.65/1.83  thf('184', plain,
% 1.65/1.83      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['9'])).
% 1.65/1.83  thf('185', plain,
% 1.65/1.83      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('split', [status(esa)], ['163'])).
% 1.65/1.83  thf('186', plain,
% 1.65/1.83      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.65/1.83      inference('split', [status(esa)], ['57'])).
% 1.65/1.83  thf('187', plain,
% 1.65/1.83      ((~ (m1_subset_1 @ sk_D @ 
% 1.65/1.83           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['185', '186'])).
% 1.65/1.83  thf('188', plain,
% 1.65/1.83      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.65/1.83         <= (~
% 1.65/1.83             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.65/1.83             (((sk_A) = (k1_xboole_0))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['184', '187'])).
% 1.65/1.83  thf('189', plain,
% 1.65/1.83      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.65/1.83       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['183', '188'])).
% 1.65/1.83  thf('190', plain,
% 1.65/1.83      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.65/1.83       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 1.65/1.83      inference('split', [status(esa)], ['57'])).
% 1.65/1.83  thf('191', plain,
% 1.65/1.83      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.65/1.83      inference('split', [status(esa)], ['163'])).
% 1.65/1.83  thf('192', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 1.65/1.83      inference('sat_resolution*', [status(thm)],
% 1.65/1.83                ['78', '180', '189', '190', '191'])).
% 1.65/1.83  thf('193', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.65/1.83      inference('simpl_trail', [status(thm)], ['164', '192'])).
% 1.65/1.83  thf('194', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.65/1.83      inference('simplify_reflect-', [status(thm)], ['162', '193'])).
% 1.65/1.83  thf('195', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['107', '194'])).
% 1.65/1.83  thf('196', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['83', '98'])).
% 1.65/1.83  thf('197', plain,
% 1.65/1.83      (![X10 : $i, X11 : $i]:
% 1.65/1.83         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t3_subset])).
% 1.65/1.83  thf('198', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 1.65/1.83      inference('sup-', [status(thm)], ['196', '197'])).
% 1.65/1.83  thf('199', plain,
% 1.65/1.83      (![X1 : $i, X3 : $i]:
% 1.65/1.83         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.65/1.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.83  thf('200', plain,
% 1.65/1.83      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 1.65/1.83        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['198', '199'])).
% 1.65/1.83  thf('201', plain,
% 1.65/1.83      (![X40 : $i, X41 : $i]:
% 1.65/1.83         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.83  thf('202', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['83', '98'])).
% 1.65/1.83  thf('203', plain,
% 1.65/1.83      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.65/1.83         (~ (zip_tseitin_0 @ X45 @ X46)
% 1.65/1.83          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 1.65/1.83          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.65/1.83  thf('204', plain,
% 1.65/1.83      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['202', '203'])).
% 1.65/1.83  thf('205', plain,
% 1.65/1.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['83', '98'])).
% 1.65/1.83  thf('206', plain,
% 1.65/1.83      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.65/1.83         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.65/1.83          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.65/1.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.65/1.83  thf('207', plain,
% 1.65/1.83      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.65/1.83      inference('sup-', [status(thm)], ['205', '206'])).
% 1.65/1.83  thf('208', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.65/1.83      inference('simplify_reflect-', [status(thm)], ['162', '193'])).
% 1.65/1.83  thf('209', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['207', '208'])).
% 1.65/1.83  thf('210', plain,
% 1.65/1.83      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.65/1.83         (((X42) != (k1_relset_1 @ X42 @ X43 @ X44))
% 1.65/1.83          | (v1_funct_2 @ X44 @ X42 @ X43)
% 1.65/1.83          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('211', plain,
% 1.65/1.83      ((((sk_A) != (sk_A))
% 1.65/1.83        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 1.65/1.83        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.65/1.83      inference('sup-', [status(thm)], ['209', '210'])).
% 1.65/1.83  thf('212', plain,
% 1.65/1.83      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 1.65/1.83        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 1.65/1.83      inference('simplify', [status(thm)], ['211'])).
% 1.65/1.83  thf('213', plain,
% 1.65/1.83      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.65/1.83         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.65/1.83      inference('split', [status(esa)], ['57'])).
% 1.65/1.83  thf('214', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.65/1.83      inference('sat_resolution*', [status(thm)], ['78', '101', '102'])).
% 1.65/1.83  thf('215', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 1.65/1.83      inference('simpl_trail', [status(thm)], ['213', '214'])).
% 1.65/1.83  thf('216', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 1.65/1.83      inference('clc', [status(thm)], ['212', '215'])).
% 1.65/1.83  thf('217', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 1.65/1.83      inference('clc', [status(thm)], ['204', '216'])).
% 1.65/1.83  thf('218', plain, (((sk_C) = (k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['201', '217'])).
% 1.65/1.83  thf('219', plain,
% 1.65/1.83      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['18'])).
% 1.65/1.83  thf('220', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.65/1.83      inference('demod', [status(thm)], ['12', '22'])).
% 1.65/1.83  thf('221', plain, (((sk_C) = (k1_xboole_0))),
% 1.65/1.83      inference('sup-', [status(thm)], ['201', '217'])).
% 1.65/1.83  thf('222', plain,
% 1.65/1.83      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['18'])).
% 1.65/1.83  thf('223', plain, (((k1_xboole_0) = (sk_D))),
% 1.65/1.83      inference('demod', [status(thm)],
% 1.65/1.83                ['200', '218', '219', '220', '221', '222'])).
% 1.65/1.83  thf('224', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.83      inference('demod', [status(thm)], ['27', '43'])).
% 1.65/1.83  thf('225', plain, (((k1_xboole_0) = (sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['195', '223', '224'])).
% 1.65/1.83  thf('226', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.83      inference('sup-', [status(thm)], ['71', '72'])).
% 1.65/1.83  thf('227', plain, ($false),
% 1.65/1.83      inference('demod', [status(thm)], ['104', '225', '226'])).
% 1.65/1.83  
% 1.65/1.83  % SZS output end Refutation
% 1.65/1.83  
% 1.65/1.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
