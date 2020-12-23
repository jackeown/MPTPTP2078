%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ezNPn0bMR4

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:08 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  191 (1022 expanded)
%              Number of leaves         :   42 ( 308 expanded)
%              Depth                    :   23
%              Number of atoms          : 1275 (13387 expanded)
%              Number of equality atoms :   97 ( 813 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','20'])).

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

thf('22',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40
       != ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    ! [X38: $i] :
      ( zip_tseitin_0 @ X38 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','32'])).

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

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('47',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['24','30'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('63',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('65',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('66',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('73',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('74',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('79',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('83',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['49'])).

thf('84',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['53','68','81','82','83'])).

thf('85',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['50','84'])).

thf('86',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['48','85'])).

thf('87',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['43','86'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('88',plain,(
    ! [X18: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['36','89'])).

thf('91',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('93',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('94',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('97',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('102',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['100','105'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('107',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X33 )
      | ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['103','104'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','110'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('115',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['53','113','114'])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['90','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','110'])).

thf('118',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('119',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('121',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('123',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','110'])).

thf('124',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('125',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','110'])).

thf('127',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('128',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['43','86'])).

thf('130',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40
       != ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('135',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['53','113','114'])).

thf('136',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['133','136'])).

thf('138',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['125','137'])).

thf('139',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['122','138'])).

thf('140',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('141',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('143',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['122','138'])).

thf('144',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['140'])).

thf('145',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['121','139','141','142','143','144'])).

thf('146',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('147',plain,(
    $false ),
    inference(demod,[status(thm)],['116','145','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ezNPn0bMR4
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.81/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.81/1.01  % Solved by: fo/fo7.sh
% 0.81/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.01  % done 958 iterations in 0.546s
% 0.81/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.81/1.01  % SZS output start Refutation
% 0.81/1.01  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.81/1.01  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.81/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.81/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.81/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.81/1.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.81/1.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.81/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/1.01  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.81/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.81/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/1.01  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.81/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.81/1.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.81/1.01  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.81/1.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.81/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.81/1.01  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.81/1.01  thf(l13_xboole_0, axiom,
% 0.81/1.01    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.81/1.01  thf('0', plain,
% 0.81/1.01      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.81/1.01      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.81/1.01  thf('1', plain,
% 0.81/1.01      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.81/1.01      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.81/1.01  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.81/1.01  thf('2', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.81/1.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.81/1.01  thf(t3_subset, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.81/1.01  thf('3', plain,
% 0.81/1.01      (![X8 : $i, X10 : $i]:
% 0.81/1.01         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.81/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/1.01  thf('4', plain,
% 0.81/1.01      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.81/1.01  thf(redefinition_k1_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.81/1.01  thf('5', plain,
% 0.81/1.01      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.81/1.01         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.81/1.01          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.81/1.01  thf('6', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['4', '5'])).
% 0.81/1.01  thf('7', plain,
% 0.81/1.01      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.81/1.01  thf(cc2_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.81/1.01  thf('8', plain,
% 0.81/1.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.01         ((v4_relat_1 @ X22 @ X23)
% 0.81/1.01          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.81/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.81/1.01  thf('9', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.81/1.01      inference('sup-', [status(thm)], ['7', '8'])).
% 0.81/1.01  thf(d18_relat_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( v1_relat_1 @ B ) =>
% 0.81/1.01       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.81/1.01  thf('10', plain,
% 0.81/1.01      (![X16 : $i, X17 : $i]:
% 0.81/1.01         (~ (v4_relat_1 @ X16 @ X17)
% 0.81/1.01          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.81/1.01          | ~ (v1_relat_1 @ X16))),
% 0.81/1.01      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.81/1.01  thf('11', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         (~ (v1_relat_1 @ k1_xboole_0)
% 0.81/1.01          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['9', '10'])).
% 0.81/1.01  thf(t113_zfmisc_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.81/1.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.81/1.01  thf('12', plain,
% 0.81/1.01      (![X6 : $i, X7 : $i]:
% 0.81/1.01         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.81/1.01  thf('13', plain,
% 0.81/1.01      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.81/1.01      inference('simplify', [status(thm)], ['12'])).
% 0.81/1.01  thf(fc6_relat_1, axiom,
% 0.81/1.01    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.81/1.01  thf('14', plain,
% 0.81/1.01      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.81/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.81/1.01  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.81/1.01      inference('sup+', [status(thm)], ['13', '14'])).
% 0.81/1.01  thf('16', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.81/1.01      inference('demod', [status(thm)], ['11', '15'])).
% 0.81/1.01  thf('17', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.81/1.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.81/1.01  thf(d10_xboole_0, axiom,
% 0.81/1.01    (![A:$i,B:$i]:
% 0.81/1.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/1.01  thf('18', plain,
% 0.81/1.01      (![X1 : $i, X3 : $i]:
% 0.81/1.01         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.81/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.01  thf('19', plain,
% 0.81/1.01      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['17', '18'])).
% 0.81/1.01  thf('20', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['16', '19'])).
% 0.81/1.01  thf('21', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.01      inference('demod', [status(thm)], ['6', '20'])).
% 0.81/1.01  thf(d1_funct_2, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.81/1.01           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.81/1.01             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.81/1.01         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.81/1.01           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.81/1.01             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.81/1.01  thf(zf_stmt_0, axiom,
% 0.81/1.01    (![C:$i,B:$i,A:$i]:
% 0.81/1.01     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.81/1.01       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.81/1.01  thf('22', plain,
% 0.81/1.01      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.81/1.01         (((X40) != (k1_relset_1 @ X40 @ X41 @ X42))
% 0.81/1.01          | (v1_funct_2 @ X42 @ X40 @ X41)
% 0.81/1.01          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('23', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         (((X1) != (k1_xboole_0))
% 0.81/1.01          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.81/1.01          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['21', '22'])).
% 0.81/1.01  thf('24', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.81/1.01          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.81/1.01      inference('simplify', [status(thm)], ['23'])).
% 0.81/1.01  thf(zf_stmt_1, axiom,
% 0.81/1.01    (![B:$i,A:$i]:
% 0.81/1.01     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.81/1.01       ( zip_tseitin_0 @ B @ A ) ))).
% 0.81/1.01  thf('25', plain,
% 0.81/1.01      (![X38 : $i, X39 : $i]:
% 0.81/1.01         ((zip_tseitin_0 @ X38 @ X39) | ((X39) != (k1_xboole_0)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.81/1.01  thf('26', plain, (![X38 : $i]: (zip_tseitin_0 @ X38 @ k1_xboole_0)),
% 0.81/1.01      inference('simplify', [status(thm)], ['25'])).
% 0.81/1.01  thf('27', plain,
% 0.81/1.01      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.81/1.01  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.81/1.01  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.81/1.01  thf(zf_stmt_4, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.81/1.01         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.81/1.01           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.81/1.01             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.81/1.01  thf('28', plain,
% 0.81/1.01      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.81/1.01         (~ (zip_tseitin_0 @ X43 @ X44)
% 0.81/1.01          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 0.81/1.01          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.81/1.01  thf('29', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.81/1.01      inference('sup-', [status(thm)], ['27', '28'])).
% 0.81/1.01  thf('30', plain,
% 0.81/1.01      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.81/1.01      inference('sup-', [status(thm)], ['26', '29'])).
% 0.81/1.01  thf('31', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.81/1.01      inference('demod', [status(thm)], ['24', '30'])).
% 0.81/1.01  thf('32', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i]:
% 0.81/1.01         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.81/1.01      inference('sup+', [status(thm)], ['1', '31'])).
% 0.81/1.01  thf('33', plain,
% 0.81/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.01         ((v1_funct_2 @ X2 @ X0 @ X1)
% 0.81/1.01          | ~ (v1_xboole_0 @ X0)
% 0.81/1.01          | ~ (v1_xboole_0 @ X2))),
% 0.81/1.01      inference('sup+', [status(thm)], ['0', '32'])).
% 0.81/1.01  thf(t8_funct_2, conjecture,
% 0.81/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.01     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.81/1.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.01       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.81/1.01         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.81/1.01           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.81/1.01             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.81/1.01  thf(zf_stmt_5, negated_conjecture,
% 0.81/1.01    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.01        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.81/1.01            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.01          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.81/1.01            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.81/1.01              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.81/1.01                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.81/1.01    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.81/1.01  thf('34', plain,
% 0.81/1.01      ((~ (v1_funct_1 @ sk_D)
% 0.81/1.01        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.81/1.01        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf('35', plain,
% 0.81/1.01      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.81/1.01         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.81/1.01      inference('split', [status(esa)], ['34'])).
% 0.81/1.01  thf('36', plain,
% 0.81/1.01      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 0.81/1.01         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['33', '35'])).
% 0.81/1.01  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf('38', plain,
% 0.81/1.01      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.81/1.01         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.81/1.01          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 0.81/1.01          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('39', plain,
% 0.81/1.01      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.81/1.01        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['37', '38'])).
% 0.81/1.01  thf('40', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf('41', plain,
% 0.81/1.01      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.81/1.01         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.81/1.01          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.81/1.01  thf('42', plain,
% 0.81/1.01      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.81/1.01      inference('sup-', [status(thm)], ['40', '41'])).
% 0.81/1.01  thf('43', plain,
% 0.81/1.01      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.81/1.01        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.81/1.01      inference('demod', [status(thm)], ['39', '42'])).
% 0.81/1.01  thf('44', plain,
% 0.81/1.01      (![X38 : $i, X39 : $i]:
% 0.81/1.01         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.81/1.01  thf('45', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf('46', plain,
% 0.81/1.01      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.81/1.01         (~ (zip_tseitin_0 @ X43 @ X44)
% 0.81/1.01          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 0.81/1.01          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.81/1.01  thf('47', plain,
% 0.81/1.01      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.81/1.01        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['45', '46'])).
% 0.81/1.01  thf('48', plain,
% 0.81/1.01      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['44', '47'])).
% 0.81/1.01  thf('49', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf('50', plain,
% 0.81/1.01      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.81/1.01      inference('split', [status(esa)], ['49'])).
% 0.81/1.01  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf('52', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.81/1.01      inference('split', [status(esa)], ['34'])).
% 0.81/1.01  thf('53', plain, (((v1_funct_1 @ sk_D))),
% 0.81/1.01      inference('sup-', [status(thm)], ['51', '52'])).
% 0.81/1.01  thf('54', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.81/1.01      inference('demod', [status(thm)], ['24', '30'])).
% 0.81/1.01  thf('55', plain,
% 0.81/1.01      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('split', [status(esa)], ['49'])).
% 0.81/1.01  thf('56', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf('57', plain,
% 0.81/1.01      (((m1_subset_1 @ sk_D @ 
% 0.81/1.01         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.81/1.01         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup+', [status(thm)], ['55', '56'])).
% 0.81/1.01  thf('58', plain,
% 0.81/1.01      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.81/1.01      inference('simplify', [status(thm)], ['12'])).
% 0.81/1.01  thf('59', plain,
% 0.81/1.01      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.81/1.01         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('demod', [status(thm)], ['57', '58'])).
% 0.81/1.01  thf('60', plain,
% 0.81/1.01      (![X8 : $i, X9 : $i]:
% 0.81/1.01         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/1.01  thf('61', plain,
% 0.81/1.01      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['59', '60'])).
% 0.81/1.01  thf('62', plain,
% 0.81/1.01      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['17', '18'])).
% 0.81/1.01  thf('63', plain,
% 0.81/1.01      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['61', '62'])).
% 0.81/1.01  thf('64', plain,
% 0.81/1.01      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('split', [status(esa)], ['49'])).
% 0.81/1.01  thf('65', plain,
% 0.81/1.01      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.81/1.01         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.81/1.01      inference('split', [status(esa)], ['34'])).
% 0.81/1.01  thf('66', plain,
% 0.81/1.01      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.81/1.01         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['64', '65'])).
% 0.81/1.01  thf('67', plain,
% 0.81/1.01      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.81/1.01         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['63', '66'])).
% 0.81/1.01  thf('68', plain,
% 0.81/1.01      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['54', '67'])).
% 0.81/1.01  thf('69', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf('70', plain,
% 0.81/1.01      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.81/1.01      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.81/1.01  thf('71', plain,
% 0.81/1.01      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.81/1.01      inference('simplify', [status(thm)], ['12'])).
% 0.81/1.01  thf('72', plain,
% 0.81/1.01      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('split', [status(esa)], ['49'])).
% 0.81/1.01  thf('73', plain,
% 0.81/1.01      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.81/1.01         <= (~
% 0.81/1.01             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.81/1.01      inference('split', [status(esa)], ['34'])).
% 0.81/1.01  thf('74', plain,
% 0.81/1.01      ((~ (m1_subset_1 @ sk_D @ 
% 0.81/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.81/1.01         <= (~
% 0.81/1.01             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.81/1.01             (((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['72', '73'])).
% 0.81/1.01  thf('75', plain,
% 0.81/1.01      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.81/1.01         <= (~
% 0.81/1.01             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.81/1.01             (((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['71', '74'])).
% 0.81/1.01  thf('76', plain,
% 0.81/1.01      ((![X0 : $i]:
% 0.81/1.01          (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.81/1.01         <= (~
% 0.81/1.01             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.81/1.01             (((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['70', '75'])).
% 0.81/1.01  thf('77', plain,
% 0.81/1.01      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.81/1.01         <= (~
% 0.81/1.01             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.81/1.01             (((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['69', '76'])).
% 0.81/1.01  thf('78', plain,
% 0.81/1.01      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.01      inference('split', [status(esa)], ['49'])).
% 0.81/1.01  thf('79', plain,
% 0.81/1.01      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.81/1.01      inference('simplify', [status(thm)], ['12'])).
% 0.81/1.01  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.81/1.01  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.81/1.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.81/1.01  thf('81', plain,
% 0.81/1.01      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.81/1.01       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.81/1.01      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.81/1.01  thf('82', plain,
% 0.81/1.01      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.81/1.01       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.81/1.01      inference('split', [status(esa)], ['34'])).
% 0.81/1.01  thf('83', plain,
% 0.81/1.01      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.81/1.01      inference('split', [status(esa)], ['49'])).
% 0.81/1.01  thf('84', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.81/1.01      inference('sat_resolution*', [status(thm)],
% 0.81/1.01                ['53', '68', '81', '82', '83'])).
% 0.81/1.01  thf('85', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.81/1.01      inference('simpl_trail', [status(thm)], ['50', '84'])).
% 0.81/1.01  thf('86', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.81/1.01      inference('simplify_reflect-', [status(thm)], ['48', '85'])).
% 0.81/1.01  thf('87', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.81/1.01      inference('demod', [status(thm)], ['43', '86'])).
% 0.81/1.01  thf(fc10_relat_1, axiom,
% 0.81/1.01    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.81/1.01  thf('88', plain,
% 0.81/1.01      (![X18 : $i]:
% 0.81/1.01         ((v1_xboole_0 @ (k1_relat_1 @ X18)) | ~ (v1_xboole_0 @ X18))),
% 0.81/1.01      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.81/1.01  thf('89', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 0.81/1.01      inference('sup+', [status(thm)], ['87', '88'])).
% 0.81/1.01  thf('90', plain,
% 0.81/1.01      ((~ (v1_xboole_0 @ sk_D)) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.81/1.01      inference('clc', [status(thm)], ['36', '89'])).
% 0.81/1.01  thf('91', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C)),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf('92', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf(redefinition_k2_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.01       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.81/1.01  thf('93', plain,
% 0.81/1.01      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.81/1.01         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.81/1.01          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.81/1.01  thf('94', plain,
% 0.81/1.01      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.81/1.01      inference('sup-', [status(thm)], ['92', '93'])).
% 0.81/1.01  thf('95', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.81/1.01      inference('demod', [status(thm)], ['91', '94'])).
% 0.81/1.01  thf('96', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf('97', plain,
% 0.81/1.01      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.01         ((v4_relat_1 @ X22 @ X23)
% 0.81/1.01          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.81/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.81/1.01  thf('98', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.81/1.01      inference('sup-', [status(thm)], ['96', '97'])).
% 0.81/1.01  thf('99', plain,
% 0.81/1.01      (![X16 : $i, X17 : $i]:
% 0.81/1.01         (~ (v4_relat_1 @ X16 @ X17)
% 0.81/1.01          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.81/1.01          | ~ (v1_relat_1 @ X16))),
% 0.81/1.01      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.81/1.01  thf('100', plain,
% 0.81/1.01      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['98', '99'])).
% 0.81/1.01  thf('101', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.01  thf(cc2_relat_1, axiom,
% 0.81/1.01    (![A:$i]:
% 0.81/1.01     ( ( v1_relat_1 @ A ) =>
% 0.81/1.01       ( ![B:$i]:
% 0.81/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.81/1.01  thf('102', plain,
% 0.81/1.01      (![X14 : $i, X15 : $i]:
% 0.81/1.01         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.81/1.01          | (v1_relat_1 @ X14)
% 0.81/1.01          | ~ (v1_relat_1 @ X15))),
% 0.81/1.01      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.81/1.01  thf('103', plain,
% 0.81/1.01      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.81/1.01      inference('sup-', [status(thm)], ['101', '102'])).
% 0.81/1.01  thf('104', plain,
% 0.81/1.01      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.81/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.81/1.01  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 0.81/1.01      inference('demod', [status(thm)], ['103', '104'])).
% 0.81/1.01  thf('106', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.81/1.01      inference('demod', [status(thm)], ['100', '105'])).
% 0.81/1.01  thf(t11_relset_1, axiom,
% 0.81/1.01    (![A:$i,B:$i,C:$i]:
% 0.81/1.01     ( ( v1_relat_1 @ C ) =>
% 0.81/1.01       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.81/1.01           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.81/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.81/1.01  thf('107', plain,
% 0.81/1.01      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.81/1.01         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 0.81/1.01          | ~ (r1_tarski @ (k2_relat_1 @ X31) @ X33)
% 0.81/1.01          | (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.81/1.01          | ~ (v1_relat_1 @ X31))),
% 0.81/1.01      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.81/1.01  thf('108', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         (~ (v1_relat_1 @ sk_D)
% 0.81/1.01          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.81/1.01          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['106', '107'])).
% 0.81/1.01  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 0.81/1.01      inference('demod', [status(thm)], ['103', '104'])).
% 0.81/1.01  thf('110', plain,
% 0.81/1.01      (![X0 : $i]:
% 0.81/1.01         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.81/1.01          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.81/1.01      inference('demod', [status(thm)], ['108', '109'])).
% 0.81/1.01  thf('111', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['95', '110'])).
% 0.81/1.01  thf('112', plain,
% 0.81/1.01      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.81/1.01         <= (~
% 0.81/1.01             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.81/1.01      inference('split', [status(esa)], ['34'])).
% 0.81/1.01  thf('113', plain,
% 0.81/1.01      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.81/1.01      inference('sup-', [status(thm)], ['111', '112'])).
% 0.81/1.01  thf('114', plain,
% 0.81/1.01      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.81/1.01       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.81/1.01       ~ ((v1_funct_1 @ sk_D))),
% 0.81/1.01      inference('split', [status(esa)], ['34'])).
% 0.81/1.01  thf('115', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.81/1.01      inference('sat_resolution*', [status(thm)], ['53', '113', '114'])).
% 0.81/1.01  thf('116', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.81/1.01      inference('simpl_trail', [status(thm)], ['90', '115'])).
% 0.81/1.01  thf('117', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['95', '110'])).
% 0.81/1.01  thf('118', plain,
% 0.81/1.01      (![X8 : $i, X9 : $i]:
% 0.81/1.01         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/1.01  thf('119', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.81/1.01      inference('sup-', [status(thm)], ['117', '118'])).
% 0.81/1.01  thf('120', plain,
% 0.81/1.01      (![X1 : $i, X3 : $i]:
% 0.81/1.01         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.81/1.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.01  thf('121', plain,
% 0.81/1.01      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 0.81/1.01        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['119', '120'])).
% 0.81/1.01  thf('122', plain,
% 0.81/1.01      (![X38 : $i, X39 : $i]:
% 0.81/1.01         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.81/1.01  thf('123', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['95', '110'])).
% 0.81/1.01  thf('124', plain,
% 0.81/1.01      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.81/1.01         (~ (zip_tseitin_0 @ X43 @ X44)
% 0.81/1.01          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 0.81/1.01          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.81/1.01  thf('125', plain,
% 0.81/1.01      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.81/1.01      inference('sup-', [status(thm)], ['123', '124'])).
% 0.81/1.01  thf('126', plain,
% 0.81/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.81/1.01      inference('sup-', [status(thm)], ['95', '110'])).
% 0.81/1.01  thf('127', plain,
% 0.81/1.01      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.81/1.01         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.81/1.01          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.81/1.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.81/1.01  thf('128', plain,
% 0.81/1.01      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.81/1.01      inference('sup-', [status(thm)], ['126', '127'])).
% 0.81/1.01  thf('129', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.81/1.01      inference('demod', [status(thm)], ['43', '86'])).
% 0.81/1.01  thf('130', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.81/1.01      inference('demod', [status(thm)], ['128', '129'])).
% 0.81/1.01  thf('131', plain,
% 0.81/1.01      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.81/1.01         (((X40) != (k1_relset_1 @ X40 @ X41 @ X42))
% 0.81/1.01          | (v1_funct_2 @ X42 @ X40 @ X41)
% 0.81/1.01          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 0.81/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.01  thf('132', plain,
% 0.81/1.01      ((((sk_A) != (sk_A))
% 0.81/1.01        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.81/1.01        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.81/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.81/1.01  thf('133', plain,
% 0.81/1.01      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.81/1.01        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.81/1.01      inference('simplify', [status(thm)], ['132'])).
% 0.81/1.01  thf('134', plain,
% 0.81/1.01      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.81/1.01         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.81/1.01      inference('split', [status(esa)], ['34'])).
% 0.81/1.01  thf('135', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.81/1.01      inference('sat_resolution*', [status(thm)], ['53', '113', '114'])).
% 0.81/1.01  thf('136', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.81/1.01      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 0.81/1.01  thf('137', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.81/1.01      inference('clc', [status(thm)], ['133', '136'])).
% 0.81/1.01  thf('138', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 0.81/1.01      inference('clc', [status(thm)], ['125', '137'])).
% 0.81/1.01  thf('139', plain, (((sk_C) = (k1_xboole_0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['122', '138'])).
% 0.81/1.01  thf('140', plain,
% 0.81/1.01      (![X6 : $i, X7 : $i]:
% 0.81/1.01         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.81/1.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.81/1.01  thf('141', plain,
% 0.81/1.01      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.01      inference('simplify', [status(thm)], ['140'])).
% 0.81/1.01  thf('142', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.81/1.01      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.81/1.01  thf('143', plain, (((sk_C) = (k1_xboole_0))),
% 0.81/1.01      inference('sup-', [status(thm)], ['122', '138'])).
% 0.81/1.01  thf('144', plain,
% 0.81/1.01      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.81/1.01      inference('simplify', [status(thm)], ['140'])).
% 0.81/1.01  thf('145', plain, (((k1_xboole_0) = (sk_D))),
% 0.81/1.01      inference('demod', [status(thm)],
% 0.81/1.01                ['121', '139', '141', '142', '143', '144'])).
% 0.81/1.01  thf('146', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.81/1.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.81/1.01  thf('147', plain, ($false),
% 0.81/1.01      inference('demod', [status(thm)], ['116', '145', '146'])).
% 0.81/1.01  
% 0.81/1.01  % SZS output end Refutation
% 0.81/1.01  
% 0.81/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
