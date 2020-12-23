%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BJpb64j9UF

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:08 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 803 expanded)
%              Number of leaves         :   44 ( 248 expanded)
%              Depth                    :   25
%              Number of atoms          : 1616 (9573 expanded)
%              Number of equality atoms :  144 ( 655 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['11','15'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','18'])).

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

thf('20',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40
       != ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,(
    ! [X38: $i] :
      ( zip_tseitin_0 @ X38 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('26',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','30'])).

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

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('43',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('44',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('58',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('65',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['22','28'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['64'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('82',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['64'])).

thf('84',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf('85',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('90',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['64'])).

thf('92',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['32'])).

thf('93',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','95'])).

thf('97',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['64'])).

thf('98',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('99',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('100',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('102',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['64'])).

thf('103',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['72','87','100','101','102'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['69','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['60','104'])).

thf('106',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['105','108'])).

thf('110',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['44','109'])).

thf('111',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','110'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('112',plain,(
    ! [X20: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['34','113'])).

thf('115',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('116',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('117',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('118',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['115','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('121',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('122',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('126',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('129',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['124','129'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('131',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X35 ) @ X36 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X37 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['127','128'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','134'])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['32'])).

thf('137',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('139',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['72','137','138'])).

thf('140',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['114','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('142',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('144',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('148',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['141','148'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('150',plain,(
    ! [X25: $i] :
      ( ( ( k2_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['127','128'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('158',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 != k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ( X45 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('159',plain,(
    ! [X44: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X44 @ k1_xboole_0 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('161',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('162',plain,(
    ! [X44: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X44 @ k1_xboole_0 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','18'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['157','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['156','168'])).

thf('170',plain,
    ( ( sk_D = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(condensation,[status(thm)],['169'])).

thf('171',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('172',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','134'])).

thf('173',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('174',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['119','134'])).

thf('176',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('177',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','110'])).

thf('179',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40
       != ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf('184',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['72','137','138'])).

thf('185',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['182','185'])).

thf('187',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['174','186'])).

thf('188',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['171','187'])).

thf('189',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('190',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['170','188','189'])).

thf('191',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('192',plain,(
    $false ),
    inference(demod,[status(thm)],['140','190','191'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BJpb64j9UF
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.01/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.01/1.21  % Solved by: fo/fo7.sh
% 1.01/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.21  % done 1334 iterations in 0.769s
% 1.01/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.01/1.21  % SZS output start Refutation
% 1.01/1.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.01/1.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.01/1.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.01/1.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.01/1.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.01/1.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.01/1.21  thf(sk_D_type, type, sk_D: $i).
% 1.01/1.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.01/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.01/1.21  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.01/1.21  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.01/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.01/1.21  thf(sk_C_type, type, sk_C: $i).
% 1.01/1.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.01/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.01/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.01/1.21  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.01/1.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.01/1.21  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.01/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.21  thf(l13_xboole_0, axiom,
% 1.01/1.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.01/1.21  thf('0', plain,
% 1.01/1.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.01/1.21  thf('1', plain,
% 1.01/1.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.01/1.21  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.01/1.21  thf('2', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.01/1.21      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.01/1.21  thf(t3_subset, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.01/1.21  thf('3', plain,
% 1.01/1.21      (![X10 : $i, X12 : $i]:
% 1.01/1.21         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.01/1.21  thf('4', plain,
% 1.01/1.21      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.21  thf(redefinition_k1_relset_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.21       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.01/1.21  thf('5', plain,
% 1.01/1.21      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.01/1.21         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 1.01/1.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.01/1.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.01/1.21  thf('6', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.21  thf('7', plain,
% 1.01/1.21      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.21  thf(cc2_relset_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.21       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.01/1.21  thf('8', plain,
% 1.01/1.21      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.01/1.21         ((v4_relat_1 @ X26 @ X27)
% 1.01/1.21          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.01/1.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.01/1.21  thf('9', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 1.01/1.21      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.21  thf(d18_relat_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ B ) =>
% 1.01/1.21       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.01/1.21  thf('10', plain,
% 1.01/1.21      (![X18 : $i, X19 : $i]:
% 1.01/1.21         (~ (v4_relat_1 @ X18 @ X19)
% 1.01/1.21          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.01/1.21          | ~ (v1_relat_1 @ X18))),
% 1.01/1.21      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.01/1.21  thf('11', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         (~ (v1_relat_1 @ k1_xboole_0)
% 1.01/1.21          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['9', '10'])).
% 1.01/1.21  thf(t113_zfmisc_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.01/1.21       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.01/1.21  thf('12', plain,
% 1.01/1.21      (![X8 : $i, X9 : $i]:
% 1.01/1.21         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.01/1.21  thf('13', plain,
% 1.01/1.21      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.01/1.21      inference('simplify', [status(thm)], ['12'])).
% 1.01/1.21  thf(fc6_relat_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.01/1.21  thf('14', plain,
% 1.01/1.21      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 1.01/1.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.01/1.21  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.01/1.21      inference('sup+', [status(thm)], ['13', '14'])).
% 1.01/1.21  thf('16', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.01/1.21      inference('demod', [status(thm)], ['11', '15'])).
% 1.01/1.21  thf(t3_xboole_1, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.01/1.21  thf('17', plain,
% 1.01/1.21      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.01/1.21  thf('18', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['16', '17'])).
% 1.01/1.21  thf('19', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.21      inference('demod', [status(thm)], ['6', '18'])).
% 1.01/1.21  thf(d1_funct_2, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.21       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.01/1.21           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.01/1.21             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.01/1.21         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.01/1.21           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.01/1.21             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.01/1.21  thf(zf_stmt_0, axiom,
% 1.01/1.21    (![C:$i,B:$i,A:$i]:
% 1.01/1.21     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.01/1.21       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.01/1.21  thf('20', plain,
% 1.01/1.21      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.01/1.21         (((X40) != (k1_relset_1 @ X40 @ X41 @ X42))
% 1.01/1.21          | (v1_funct_2 @ X42 @ X40 @ X41)
% 1.01/1.21          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('21', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((X1) != (k1_xboole_0))
% 1.01/1.21          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.01/1.21          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['19', '20'])).
% 1.01/1.21  thf('22', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.01/1.21          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.01/1.21      inference('simplify', [status(thm)], ['21'])).
% 1.01/1.21  thf(zf_stmt_1, axiom,
% 1.01/1.21    (![B:$i,A:$i]:
% 1.01/1.21     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.01/1.21       ( zip_tseitin_0 @ B @ A ) ))).
% 1.01/1.21  thf('23', plain,
% 1.01/1.21      (![X38 : $i, X39 : $i]:
% 1.01/1.21         ((zip_tseitin_0 @ X38 @ X39) | ((X39) != (k1_xboole_0)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.21  thf('24', plain, (![X38 : $i]: (zip_tseitin_0 @ X38 @ k1_xboole_0)),
% 1.01/1.21      inference('simplify', [status(thm)], ['23'])).
% 1.01/1.21  thf('25', plain,
% 1.01/1.21      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.21  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.01/1.21  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.01/1.21  thf(zf_stmt_4, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.21       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.01/1.21         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.01/1.21           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.01/1.21             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.01/1.21  thf('26', plain,
% 1.01/1.21      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.01/1.21         (~ (zip_tseitin_0 @ X43 @ X44)
% 1.01/1.21          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 1.01/1.21          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.01/1.21  thf('27', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.01/1.21      inference('sup-', [status(thm)], ['25', '26'])).
% 1.01/1.21  thf('28', plain,
% 1.01/1.21      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.01/1.21      inference('sup-', [status(thm)], ['24', '27'])).
% 1.01/1.21  thf('29', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.01/1.21      inference('demod', [status(thm)], ['22', '28'])).
% 1.01/1.21  thf('30', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.21      inference('sup+', [status(thm)], ['1', '29'])).
% 1.01/1.21  thf('31', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         ((v1_funct_2 @ X2 @ X0 @ X1)
% 1.01/1.21          | ~ (v1_xboole_0 @ X0)
% 1.01/1.21          | ~ (v1_xboole_0 @ X2))),
% 1.01/1.21      inference('sup+', [status(thm)], ['0', '30'])).
% 1.01/1.21  thf(t8_funct_2, conjecture,
% 1.01/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.21     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.01/1.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.01/1.21       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.01/1.21         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.01/1.21           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.01/1.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.01/1.21  thf(zf_stmt_5, negated_conjecture,
% 1.01/1.21    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.21        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.01/1.21            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.01/1.21          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.01/1.21            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.01/1.21              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.01/1.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.01/1.21    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 1.01/1.21  thf('32', plain,
% 1.01/1.21      ((~ (v1_funct_1 @ sk_D)
% 1.01/1.21        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 1.01/1.21        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('33', plain,
% 1.01/1.21      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.01/1.21         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.01/1.21      inference('split', [status(esa)], ['32'])).
% 1.01/1.21  thf('34', plain,
% 1.01/1.21      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 1.01/1.21         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['31', '33'])).
% 1.01/1.21  thf('35', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('36', plain,
% 1.01/1.21      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.01/1.21         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 1.01/1.21          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 1.01/1.21          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('37', plain,
% 1.01/1.21      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.01/1.21        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['35', '36'])).
% 1.01/1.21  thf('38', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('39', plain,
% 1.01/1.21      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.01/1.21         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 1.01/1.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.01/1.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.01/1.21  thf('40', plain,
% 1.01/1.21      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.01/1.21      inference('sup-', [status(thm)], ['38', '39'])).
% 1.01/1.21  thf('41', plain,
% 1.01/1.21      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.01/1.21        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.01/1.21      inference('demod', [status(thm)], ['37', '40'])).
% 1.01/1.21  thf('42', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('43', plain,
% 1.01/1.21      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.01/1.21         (~ (zip_tseitin_0 @ X43 @ X44)
% 1.01/1.21          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 1.01/1.21          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.01/1.21  thf('44', plain,
% 1.01/1.21      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.01/1.21        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.01/1.21      inference('sup-', [status(thm)], ['42', '43'])).
% 1.01/1.21  thf('45', plain,
% 1.01/1.21      (![X38 : $i, X39 : $i]:
% 1.01/1.21         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.21  thf('46', plain,
% 1.01/1.21      (![X8 : $i, X9 : $i]:
% 1.01/1.21         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.01/1.21  thf('47', plain,
% 1.01/1.21      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.21      inference('simplify', [status(thm)], ['46'])).
% 1.01/1.21  thf('48', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.01/1.21      inference('sup+', [status(thm)], ['45', '47'])).
% 1.01/1.21  thf('49', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('50', plain,
% 1.01/1.21      (![X10 : $i, X11 : $i]:
% 1.01/1.21         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.01/1.21  thf('51', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 1.01/1.21      inference('sup-', [status(thm)], ['49', '50'])).
% 1.01/1.21  thf(d10_xboole_0, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.01/1.21  thf('52', plain,
% 1.01/1.21      (![X2 : $i, X4 : $i]:
% 1.01/1.21         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.01/1.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.01/1.21  thf('53', plain,
% 1.01/1.21      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_D)
% 1.01/1.21        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['51', '52'])).
% 1.01/1.21  thf('54', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         (~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 1.01/1.21          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 1.01/1.21          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['48', '53'])).
% 1.01/1.21  thf('55', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.01/1.21      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.01/1.21  thf('56', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 1.01/1.21          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 1.01/1.21      inference('demod', [status(thm)], ['54', '55'])).
% 1.01/1.21  thf('57', plain,
% 1.01/1.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.01/1.21  thf('58', plain,
% 1.01/1.21      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.21      inference('simplify', [status(thm)], ['46'])).
% 1.01/1.21  thf('59', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.21      inference('sup+', [status(thm)], ['57', '58'])).
% 1.01/1.21  thf('60', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         (((sk_D) = (k1_xboole_0))
% 1.01/1.21          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 1.01/1.21          | ~ (v1_xboole_0 @ sk_B_1))),
% 1.01/1.21      inference('sup+', [status(thm)], ['56', '59'])).
% 1.01/1.21  thf('61', plain,
% 1.01/1.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.01/1.21  thf('62', plain,
% 1.01/1.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.01/1.21  thf('63', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.01/1.21      inference('sup+', [status(thm)], ['61', '62'])).
% 1.01/1.21  thf('64', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('65', plain,
% 1.01/1.21      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.01/1.21      inference('split', [status(esa)], ['64'])).
% 1.01/1.21  thf('66', plain,
% 1.01/1.21      ((![X0 : $i]:
% 1.01/1.21          (((X0) != (k1_xboole_0))
% 1.01/1.21           | ~ (v1_xboole_0 @ X0)
% 1.01/1.21           | ~ (v1_xboole_0 @ sk_B_1)))
% 1.01/1.21         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['63', '65'])).
% 1.01/1.21  thf('67', plain,
% 1.01/1.21      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.01/1.21         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.01/1.21      inference('simplify', [status(thm)], ['66'])).
% 1.01/1.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.01/1.21  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.01/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.01/1.21  thf('69', plain,
% 1.01/1.21      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.01/1.21      inference('simplify_reflect+', [status(thm)], ['67', '68'])).
% 1.01/1.21  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('71', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.01/1.21      inference('split', [status(esa)], ['32'])).
% 1.01/1.21  thf('72', plain, (((v1_funct_1 @ sk_D))),
% 1.01/1.21      inference('sup-', [status(thm)], ['70', '71'])).
% 1.01/1.21  thf('73', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.01/1.21      inference('demod', [status(thm)], ['22', '28'])).
% 1.01/1.21  thf('74', plain,
% 1.01/1.21      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('split', [status(esa)], ['64'])).
% 1.01/1.21  thf('75', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('76', plain,
% 1.01/1.21      (((m1_subset_1 @ sk_D @ 
% 1.01/1.21         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.01/1.21         <= ((((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('sup+', [status(thm)], ['74', '75'])).
% 1.01/1.21  thf('77', plain,
% 1.01/1.21      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.01/1.21      inference('simplify', [status(thm)], ['12'])).
% 1.01/1.21  thf('78', plain,
% 1.01/1.21      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.01/1.21         <= ((((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('demod', [status(thm)], ['76', '77'])).
% 1.01/1.21  thf('79', plain,
% 1.01/1.21      (![X10 : $i, X11 : $i]:
% 1.01/1.21         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.01/1.21  thf('80', plain,
% 1.01/1.21      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['78', '79'])).
% 1.01/1.21  thf('81', plain,
% 1.01/1.21      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.01/1.21  thf('82', plain,
% 1.01/1.21      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['80', '81'])).
% 1.01/1.21  thf('83', plain,
% 1.01/1.21      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('split', [status(esa)], ['64'])).
% 1.01/1.21  thf('84', plain,
% 1.01/1.21      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.01/1.21         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.01/1.21      inference('split', [status(esa)], ['32'])).
% 1.01/1.21  thf('85', plain,
% 1.01/1.21      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 1.01/1.21         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['83', '84'])).
% 1.01/1.21  thf('86', plain,
% 1.01/1.21      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 1.01/1.21         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['82', '85'])).
% 1.01/1.21  thf('87', plain,
% 1.01/1.21      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['73', '86'])).
% 1.01/1.21  thf('88', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('89', plain,
% 1.01/1.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.01/1.21  thf('90', plain,
% 1.01/1.21      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.01/1.21      inference('simplify', [status(thm)], ['12'])).
% 1.01/1.21  thf('91', plain,
% 1.01/1.21      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('split', [status(esa)], ['64'])).
% 1.01/1.21  thf('92', plain,
% 1.01/1.21      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.01/1.21         <= (~
% 1.01/1.21             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.01/1.21      inference('split', [status(esa)], ['32'])).
% 1.01/1.21  thf('93', plain,
% 1.01/1.21      ((~ (m1_subset_1 @ sk_D @ 
% 1.01/1.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 1.01/1.21         <= (~
% 1.01/1.21             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.01/1.21             (((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['91', '92'])).
% 1.01/1.21  thf('94', plain,
% 1.01/1.21      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.01/1.21         <= (~
% 1.01/1.21             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.01/1.21             (((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['90', '93'])).
% 1.01/1.21  thf('95', plain,
% 1.01/1.21      ((![X0 : $i]:
% 1.01/1.21          (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 1.01/1.21         <= (~
% 1.01/1.21             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.01/1.21             (((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['89', '94'])).
% 1.01/1.21  thf('96', plain,
% 1.01/1.21      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.01/1.21         <= (~
% 1.01/1.21             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 1.01/1.21             (((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['88', '95'])).
% 1.01/1.21  thf('97', plain,
% 1.01/1.21      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.01/1.21      inference('split', [status(esa)], ['64'])).
% 1.01/1.21  thf('98', plain,
% 1.01/1.21      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.01/1.21      inference('simplify', [status(thm)], ['12'])).
% 1.01/1.21  thf('99', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.01/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.01/1.21  thf('100', plain,
% 1.01/1.21      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.01/1.21       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.01/1.21      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 1.01/1.21  thf('101', plain,
% 1.01/1.21      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.01/1.21       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 1.01/1.21      inference('split', [status(esa)], ['32'])).
% 1.01/1.21  thf('102', plain,
% 1.01/1.21      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.01/1.21      inference('split', [status(esa)], ['64'])).
% 1.01/1.21  thf('103', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 1.01/1.21      inference('sat_resolution*', [status(thm)],
% 1.01/1.21                ['72', '87', '100', '101', '102'])).
% 1.01/1.21  thf('104', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.01/1.21      inference('simpl_trail', [status(thm)], ['69', '103'])).
% 1.01/1.21  thf('105', plain,
% 1.01/1.21      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 1.01/1.21      inference('clc', [status(thm)], ['60', '104'])).
% 1.01/1.21  thf('106', plain,
% 1.01/1.21      (![X38 : $i, X39 : $i]:
% 1.01/1.21         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.21  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.01/1.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.01/1.21  thf('108', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.01/1.21      inference('sup+', [status(thm)], ['106', '107'])).
% 1.01/1.21  thf('109', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 1.01/1.21      inference('clc', [status(thm)], ['105', '108'])).
% 1.01/1.21  thf('110', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 1.01/1.21      inference('demod', [status(thm)], ['44', '109'])).
% 1.01/1.21  thf('111', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.01/1.21      inference('demod', [status(thm)], ['41', '110'])).
% 1.01/1.21  thf(fc10_relat_1, axiom,
% 1.01/1.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 1.01/1.21  thf('112', plain,
% 1.01/1.21      (![X20 : $i]:
% 1.01/1.21         ((v1_xboole_0 @ (k1_relat_1 @ X20)) | ~ (v1_xboole_0 @ X20))),
% 1.01/1.21      inference('cnf', [status(esa)], [fc10_relat_1])).
% 1.01/1.21  thf('113', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 1.01/1.21      inference('sup+', [status(thm)], ['111', '112'])).
% 1.01/1.21  thf('114', plain,
% 1.01/1.21      ((~ (v1_xboole_0 @ sk_D)) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.01/1.21      inference('clc', [status(thm)], ['34', '113'])).
% 1.01/1.21  thf('115', plain,
% 1.01/1.21      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('116', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf(redefinition_k2_relset_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.21       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.01/1.21  thf('117', plain,
% 1.01/1.21      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.01/1.21         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 1.01/1.21          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 1.01/1.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.01/1.21  thf('118', plain,
% 1.01/1.21      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.01/1.21      inference('sup-', [status(thm)], ['116', '117'])).
% 1.01/1.21  thf('119', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 1.01/1.21      inference('demod', [status(thm)], ['115', '118'])).
% 1.01/1.21  thf('120', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf('121', plain,
% 1.01/1.21      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.01/1.21         ((v4_relat_1 @ X26 @ X27)
% 1.01/1.21          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.01/1.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.01/1.21  thf('122', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.01/1.21      inference('sup-', [status(thm)], ['120', '121'])).
% 1.01/1.21  thf('123', plain,
% 1.01/1.21      (![X18 : $i, X19 : $i]:
% 1.01/1.21         (~ (v4_relat_1 @ X18 @ X19)
% 1.01/1.21          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.01/1.21          | ~ (v1_relat_1 @ X18))),
% 1.01/1.21      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.01/1.21  thf('124', plain,
% 1.01/1.21      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 1.01/1.21      inference('sup-', [status(thm)], ['122', '123'])).
% 1.01/1.21  thf('125', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.21  thf(cc2_relat_1, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( v1_relat_1 @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.01/1.21  thf('126', plain,
% 1.01/1.21      (![X16 : $i, X17 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.01/1.21          | (v1_relat_1 @ X16)
% 1.01/1.21          | ~ (v1_relat_1 @ X17))),
% 1.01/1.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.01/1.21  thf('127', plain,
% 1.01/1.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 1.01/1.21      inference('sup-', [status(thm)], ['125', '126'])).
% 1.01/1.21  thf('128', plain,
% 1.01/1.21      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 1.01/1.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.01/1.21  thf('129', plain, ((v1_relat_1 @ sk_D)),
% 1.01/1.21      inference('demod', [status(thm)], ['127', '128'])).
% 1.01/1.21  thf('130', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 1.01/1.22      inference('demod', [status(thm)], ['124', '129'])).
% 1.01/1.22  thf(t11_relset_1, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i]:
% 1.01/1.22     ( ( v1_relat_1 @ C ) =>
% 1.01/1.22       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.01/1.22           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.01/1.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.01/1.22  thf('131', plain,
% 1.01/1.22      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.01/1.22         (~ (r1_tarski @ (k1_relat_1 @ X35) @ X36)
% 1.01/1.22          | ~ (r1_tarski @ (k2_relat_1 @ X35) @ X37)
% 1.01/1.22          | (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.01/1.22          | ~ (v1_relat_1 @ X35))),
% 1.01/1.22      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.01/1.22  thf('132', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (v1_relat_1 @ sk_D)
% 1.01/1.22          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.01/1.22          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['130', '131'])).
% 1.01/1.22  thf('133', plain, ((v1_relat_1 @ sk_D)),
% 1.01/1.22      inference('demod', [status(thm)], ['127', '128'])).
% 1.01/1.22  thf('134', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.01/1.22          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.01/1.22      inference('demod', [status(thm)], ['132', '133'])).
% 1.01/1.22  thf('135', plain,
% 1.01/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['119', '134'])).
% 1.01/1.22  thf('136', plain,
% 1.01/1.22      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 1.01/1.22      inference('split', [status(esa)], ['32'])).
% 1.01/1.22  thf('137', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['135', '136'])).
% 1.01/1.22  thf('138', plain,
% 1.01/1.22      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 1.01/1.22       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 1.01/1.22       ~ ((v1_funct_1 @ sk_D))),
% 1.01/1.22      inference('split', [status(esa)], ['32'])).
% 1.01/1.22  thf('139', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.01/1.22      inference('sat_resolution*', [status(thm)], ['72', '137', '138'])).
% 1.01/1.22  thf('140', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.01/1.22      inference('simpl_trail', [status(thm)], ['114', '139'])).
% 1.01/1.22  thf('141', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.01/1.22      inference('sup+', [status(thm)], ['106', '107'])).
% 1.01/1.22  thf('142', plain,
% 1.01/1.22      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.01/1.22  thf('143', plain,
% 1.01/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.01/1.22  thf('144', plain,
% 1.01/1.22      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 1.01/1.22      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.01/1.22  thf('145', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (~ (r1_tarski @ X1 @ X0)
% 1.01/1.22          | ~ (v1_xboole_0 @ X0)
% 1.01/1.22          | ((X1) = (k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['143', '144'])).
% 1.01/1.22  thf('146', plain,
% 1.01/1.22      ((((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 1.01/1.22        | ~ (v1_xboole_0 @ sk_C))),
% 1.01/1.22      inference('sup-', [status(thm)], ['142', '145'])).
% 1.01/1.22  thf('147', plain,
% 1.01/1.22      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.01/1.22      inference('sup-', [status(thm)], ['116', '117'])).
% 1.01/1.22  thf('148', plain,
% 1.01/1.22      ((((k2_relat_1 @ sk_D) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C))),
% 1.01/1.22      inference('demod', [status(thm)], ['146', '147'])).
% 1.01/1.22  thf('149', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((zip_tseitin_0 @ sk_C @ X0) | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['141', '148'])).
% 1.01/1.22  thf(t64_relat_1, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( v1_relat_1 @ A ) =>
% 1.01/1.22       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.01/1.22           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.01/1.22         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.01/1.22  thf('150', plain,
% 1.01/1.22      (![X25 : $i]:
% 1.01/1.22         (((k2_relat_1 @ X25) != (k1_xboole_0))
% 1.01/1.22          | ((X25) = (k1_xboole_0))
% 1.01/1.22          | ~ (v1_relat_1 @ X25))),
% 1.01/1.22      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.01/1.22  thf('151', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((k1_xboole_0) != (k1_xboole_0))
% 1.01/1.22          | (zip_tseitin_0 @ sk_C @ X0)
% 1.01/1.22          | ~ (v1_relat_1 @ sk_D)
% 1.01/1.22          | ((sk_D) = (k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['149', '150'])).
% 1.01/1.22  thf('152', plain, ((v1_relat_1 @ sk_D)),
% 1.01/1.22      inference('demod', [status(thm)], ['127', '128'])).
% 1.01/1.22  thf('153', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((k1_xboole_0) != (k1_xboole_0))
% 1.01/1.22          | (zip_tseitin_0 @ sk_C @ X0)
% 1.01/1.22          | ((sk_D) = (k1_xboole_0)))),
% 1.01/1.22      inference('demod', [status(thm)], ['151', '152'])).
% 1.01/1.22  thf('154', plain,
% 1.01/1.22      (![X0 : $i]: (((sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C @ X0))),
% 1.01/1.22      inference('simplify', [status(thm)], ['153'])).
% 1.01/1.22  thf('155', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.01/1.22      inference('sup-', [status(thm)], ['25', '26'])).
% 1.01/1.22  thf('156', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((sk_D) = (k1_xboole_0)) | (zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['154', '155'])).
% 1.01/1.22  thf('157', plain,
% 1.01/1.22      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.01/1.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.01/1.22  thf('158', plain,
% 1.01/1.22      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.01/1.22         (((X43) != (k1_xboole_0))
% 1.01/1.22          | ((X44) = (k1_xboole_0))
% 1.01/1.22          | (v1_funct_2 @ X45 @ X44 @ X43)
% 1.01/1.22          | ((X45) != (k1_xboole_0))
% 1.01/1.22          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.01/1.22  thf('159', plain,
% 1.01/1.22      (![X44 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 1.01/1.22             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ k1_xboole_0)))
% 1.01/1.22          | (v1_funct_2 @ k1_xboole_0 @ X44 @ k1_xboole_0)
% 1.01/1.22          | ((X44) = (k1_xboole_0)))),
% 1.01/1.22      inference('simplify', [status(thm)], ['158'])).
% 1.01/1.22  thf('160', plain,
% 1.01/1.22      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.22      inference('simplify', [status(thm)], ['46'])).
% 1.01/1.22  thf('161', plain,
% 1.01/1.22      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.22  thf('162', plain,
% 1.01/1.22      (![X44 : $i]:
% 1.01/1.22         ((v1_funct_2 @ k1_xboole_0 @ X44 @ k1_xboole_0)
% 1.01/1.22          | ((X44) = (k1_xboole_0)))),
% 1.01/1.22      inference('demod', [status(thm)], ['159', '160', '161'])).
% 1.01/1.22  thf('163', plain,
% 1.01/1.22      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.01/1.22         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 1.01/1.22          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 1.01/1.22          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('164', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((X0) = (k1_xboole_0))
% 1.01/1.22          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.01/1.22          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['162', '163'])).
% 1.01/1.22  thf('165', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.22      inference('demod', [status(thm)], ['6', '18'])).
% 1.01/1.22  thf('166', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((X0) = (k1_xboole_0))
% 1.01/1.22          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.01/1.22          | ((X0) = (k1_xboole_0)))),
% 1.01/1.22      inference('demod', [status(thm)], ['164', '165'])).
% 1.01/1.22  thf('167', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.01/1.22          | ((X0) = (k1_xboole_0)))),
% 1.01/1.22      inference('simplify', [status(thm)], ['166'])).
% 1.01/1.22  thf('168', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.01/1.22          | ~ (v1_xboole_0 @ X0)
% 1.01/1.22          | ((X1) = (k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['157', '167'])).
% 1.01/1.22  thf('169', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((sk_D) = (k1_xboole_0))
% 1.01/1.22          | ((X0) = (k1_xboole_0))
% 1.01/1.22          | ~ (v1_xboole_0 @ sk_C))),
% 1.01/1.22      inference('sup-', [status(thm)], ['156', '168'])).
% 1.01/1.22  thf('170', plain, ((((sk_D) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C))),
% 1.01/1.22      inference('condensation', [status(thm)], ['169'])).
% 1.01/1.22  thf('171', plain,
% 1.01/1.22      (![X38 : $i, X39 : $i]:
% 1.01/1.22         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.22  thf('172', plain,
% 1.01/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['119', '134'])).
% 1.01/1.22  thf('173', plain,
% 1.01/1.22      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.01/1.22         (~ (zip_tseitin_0 @ X43 @ X44)
% 1.01/1.22          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 1.01/1.22          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.01/1.22  thf('174', plain,
% 1.01/1.22      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['172', '173'])).
% 1.01/1.22  thf('175', plain,
% 1.01/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['119', '134'])).
% 1.01/1.22  thf('176', plain,
% 1.01/1.22      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.01/1.22         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 1.01/1.22          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.01/1.22      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.01/1.22  thf('177', plain,
% 1.01/1.22      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.01/1.22      inference('sup-', [status(thm)], ['175', '176'])).
% 1.01/1.22  thf('178', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.01/1.22      inference('demod', [status(thm)], ['41', '110'])).
% 1.01/1.22  thf('179', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 1.01/1.22      inference('demod', [status(thm)], ['177', '178'])).
% 1.01/1.22  thf('180', plain,
% 1.01/1.22      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.01/1.22         (((X40) != (k1_relset_1 @ X40 @ X41 @ X42))
% 1.01/1.22          | (v1_funct_2 @ X42 @ X40 @ X41)
% 1.01/1.22          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('181', plain,
% 1.01/1.22      ((((sk_A) != (sk_A))
% 1.01/1.22        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 1.01/1.22        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.01/1.22      inference('sup-', [status(thm)], ['179', '180'])).
% 1.01/1.22  thf('182', plain,
% 1.01/1.22      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 1.01/1.22        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 1.01/1.22      inference('simplify', [status(thm)], ['181'])).
% 1.01/1.22  thf('183', plain,
% 1.01/1.22      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 1.01/1.22         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 1.01/1.22      inference('split', [status(esa)], ['32'])).
% 1.01/1.22  thf('184', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 1.01/1.22      inference('sat_resolution*', [status(thm)], ['72', '137', '138'])).
% 1.01/1.22  thf('185', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 1.01/1.22      inference('simpl_trail', [status(thm)], ['183', '184'])).
% 1.01/1.22  thf('186', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 1.01/1.22      inference('clc', [status(thm)], ['182', '185'])).
% 1.01/1.22  thf('187', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 1.01/1.22      inference('clc', [status(thm)], ['174', '186'])).
% 1.01/1.22  thf('188', plain, (((sk_C) = (k1_xboole_0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['171', '187'])).
% 1.01/1.22  thf('189', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.01/1.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.01/1.22  thf('190', plain, (((sk_D) = (k1_xboole_0))),
% 1.01/1.22      inference('demod', [status(thm)], ['170', '188', '189'])).
% 1.01/1.22  thf('191', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.01/1.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.01/1.22  thf('192', plain, ($false),
% 1.01/1.22      inference('demod', [status(thm)], ['140', '190', '191'])).
% 1.01/1.22  
% 1.01/1.22  % SZS output end Refutation
% 1.01/1.22  
% 1.01/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
