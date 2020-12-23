%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gnKwL4BoDo

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:10 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  158 (2425 expanded)
%              Number of leaves         :   31 ( 681 expanded)
%              Depth                    :   28
%              Number of atoms          : 1111 (35086 expanded)
%              Number of equality atoms :  108 (2404 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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

thf(zf_stmt_0,negated_conjecture,(
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

thf('0',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['26'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['26'])).

thf('49',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['44','47','48'])).

thf('50',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['41','49'])).

thf('51',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('52',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('63',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('67',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('72',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('77',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['50','78'])).

thf('80',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('81',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','81'])).

thf('83',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['22','82'])).

thf('84',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['17','83'])).

thf('85',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['10','84'])).

thf('86',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('87',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf('90',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['44','47','48'])).

thf('91',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('95',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['88','91'])).

thf('99',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('102',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('107',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('108',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('110',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('111',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('112',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['105','106','108','109','110','111'])).

thf('113',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25 != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ( X27 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('114',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('117',plain,(
    ! [X26: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['89','90'])).

thf('119',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf('120',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['105','106','108','109','110','111'])).

thf('122',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['100','112','123','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gnKwL4BoDo
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:20:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 268 iterations in 0.241s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.54/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.75  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.54/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.75  thf(t8_funct_2, conjecture,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.75       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.54/0.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.54/0.75           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.54/0.75             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.75            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.75          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.54/0.75            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.54/0.75              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.54/0.75                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.54/0.75  thf('0', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('1', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.75         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.54/0.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.75  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.75  thf('4', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(t14_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.54/0.75       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.54/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.54/0.75          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17)))
% 0.54/0.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.54/0.75      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.54/0.75  thf('7', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.54/0.75          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['4', '7'])).
% 0.54/0.75  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.54/0.75         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.54/0.75          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.75  thf('10', plain,
% 0.54/0.75      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.75  thf('11', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
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
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.75         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.54/0.75          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.54/0.75          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.54/0.75        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.75  thf('14', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('15', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.54/0.75         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.54/0.75          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.54/0.75      inference('demod', [status(thm)], ['13', '16'])).
% 0.54/0.75  thf(zf_stmt_2, axiom,
% 0.54/0.75    (![B:$i,A:$i]:
% 0.54/0.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.75       ( zip_tseitin_0 @ B @ A ) ))).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
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
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.54/0.75         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.54/0.75          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['18', '21'])).
% 0.54/0.75  thf('23', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['23'])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['23'])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      ((~ (v1_funct_1 @ sk_D)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.54/0.75        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('27', plain,
% 0.54/0.75      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.54/0.75         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.54/0.75      inference('split', [status(esa)], ['26'])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.54/0.75         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['25', '27'])).
% 0.54/0.75  thf(t113_zfmisc_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.75  thf('29', plain,
% 0.54/0.75      (![X5 : $i, X6 : $i]:
% 0.54/0.75         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['29'])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['23'])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      (((m1_subset_1 @ sk_D @ 
% 0.54/0.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['31', '32'])).
% 0.54/0.75  thf('34', plain,
% 0.54/0.75      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['30', '33'])).
% 0.54/0.75  thf(t3_subset, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.75  thf('35', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]:
% 0.54/0.75         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.75  thf('36', plain,
% 0.54/0.75      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['34', '35'])).
% 0.54/0.75  thf(d10_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.75  thf('37', plain,
% 0.54/0.75      (![X0 : $i, X2 : $i]:
% 0.54/0.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['36', '37'])).
% 0.54/0.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.75  thf('39', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf('40', plain,
% 0.54/0.75      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['38', '39'])).
% 0.54/0.75  thf('41', plain,
% 0.54/0.75      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.54/0.75         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['28', '40'])).
% 0.54/0.75  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('43', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.54/0.75      inference('split', [status(esa)], ['26'])).
% 0.54/0.75  thf('44', plain, (((v1_funct_1 @ sk_D))),
% 0.54/0.75      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.75  thf('45', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['4', '7'])).
% 0.54/0.75  thf('46', plain,
% 0.54/0.75      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.54/0.75         <= (~
% 0.54/0.75             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.54/0.75      inference('split', [status(esa)], ['26'])).
% 0.54/0.75  thf('47', plain,
% 0.54/0.75      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['45', '46'])).
% 0.54/0.75  thf('48', plain,
% 0.54/0.75      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.54/0.75       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.54/0.75       ~ ((v1_funct_1 @ sk_D))),
% 0.54/0.75      inference('split', [status(esa)], ['26'])).
% 0.54/0.75  thf('49', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.54/0.75      inference('sat_resolution*', [status(thm)], ['44', '47', '48'])).
% 0.54/0.75  thf('50', plain,
% 0.54/0.75      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['41', '49'])).
% 0.54/0.75  thf('51', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.75  thf('52', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.54/0.75      inference('simplify', [status(thm)], ['51'])).
% 0.54/0.75  thf('53', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      (![X7 : $i, X9 : $i]:
% 0.54/0.75         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.75  thf('55', plain,
% 0.54/0.75      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('56', plain,
% 0.54/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.54/0.75         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.54/0.75          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.75  thf('57', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['55', '56'])).
% 0.54/0.75  thf('58', plain,
% 0.54/0.75      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['52', '57'])).
% 0.54/0.75  thf('59', plain,
% 0.54/0.75      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['23'])).
% 0.54/0.75  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('61', plain,
% 0.54/0.75      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['59', '60'])).
% 0.54/0.75  thf('62', plain,
% 0.54/0.75      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['38', '39'])).
% 0.54/0.75  thf('63', plain,
% 0.54/0.75      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['61', '62'])).
% 0.54/0.75  thf('64', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.75         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.54/0.75          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.54/0.75          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.75  thf('65', plain,
% 0.54/0.75      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)
% 0.54/0.75         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0))))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['63', '64'])).
% 0.54/0.75  thf('66', plain,
% 0.54/0.75      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('67', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.54/0.75         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.54/0.75          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.75  thf('68', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['66', '67'])).
% 0.54/0.75  thf('69', plain,
% 0.54/0.75      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)
% 0.54/0.75         | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['65', '68'])).
% 0.54/0.75  thf('70', plain,
% 0.54/0.75      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['58', '69'])).
% 0.54/0.75  thf('71', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['66', '67'])).
% 0.54/0.75  thf('72', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.75         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.54/0.75          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.54/0.75          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.75  thf('73', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((X1) != (k1_relat_1 @ k1_xboole_0))
% 0.54/0.75          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.54/0.75          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['71', '72'])).
% 0.54/0.75  thf('74', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 0.54/0.75          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['73'])).
% 0.54/0.75  thf('75', plain,
% 0.54/0.75      ((![X0 : $i]:
% 0.54/0.75          (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.54/0.75           | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['70', '74'])).
% 0.54/0.75  thf('76', plain,
% 0.54/0.75      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['52', '57'])).
% 0.54/0.75  thf('77', plain,
% 0.54/0.75      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['58', '69'])).
% 0.54/0.75  thf('78', plain,
% 0.54/0.75      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 0.54/0.75         <= ((((sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.54/0.75  thf('79', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['50', '78'])).
% 0.54/0.75  thf('80', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.54/0.75      inference('split', [status(esa)], ['23'])).
% 0.54/0.75  thf('81', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 0.54/0.75  thf('82', plain, (((sk_B) != (k1_xboole_0))),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['24', '81'])).
% 0.54/0.75  thf('83', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['22', '82'])).
% 0.54/0.75  thf('84', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.54/0.75      inference('demod', [status(thm)], ['17', '83'])).
% 0.54/0.75  thf('85', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['10', '84'])).
% 0.54/0.75  thf('86', plain,
% 0.54/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.75         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.54/0.75          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.54/0.75          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.75  thf('87', plain,
% 0.54/0.75      ((((sk_A) != (sk_A))
% 0.54/0.75        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.54/0.75        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['85', '86'])).
% 0.54/0.75  thf('88', plain,
% 0.54/0.75      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.54/0.75        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.54/0.75      inference('simplify', [status(thm)], ['87'])).
% 0.54/0.75  thf('89', plain,
% 0.54/0.75      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.54/0.75         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.54/0.75      inference('split', [status(esa)], ['26'])).
% 0.54/0.75  thf('90', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.54/0.75      inference('sat_resolution*', [status(thm)], ['44', '47', '48'])).
% 0.54/0.75  thf('91', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['89', '90'])).
% 0.54/0.75  thf('92', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.54/0.75      inference('clc', [status(thm)], ['88', '91'])).
% 0.54/0.75  thf('93', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i]:
% 0.54/0.75         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.75  thf('94', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['4', '7'])).
% 0.54/0.75  thf('95', plain,
% 0.54/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.54/0.75         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.54/0.75          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.75  thf('96', plain,
% 0.54/0.75      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['94', '95'])).
% 0.54/0.75  thf('97', plain,
% 0.54/0.75      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['93', '96'])).
% 0.54/0.75  thf('98', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.54/0.75      inference('clc', [status(thm)], ['88', '91'])).
% 0.54/0.75  thf('99', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['97', '98'])).
% 0.54/0.75  thf('100', plain, (~ (zip_tseitin_1 @ sk_D @ k1_xboole_0 @ sk_A)),
% 0.54/0.75      inference('demod', [status(thm)], ['92', '99'])).
% 0.54/0.75  thf('101', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['4', '7'])).
% 0.54/0.75  thf('102', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]:
% 0.54/0.75         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.75  thf('103', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['101', '102'])).
% 0.54/0.75  thf('104', plain,
% 0.54/0.75      (![X0 : $i, X2 : $i]:
% 0.54/0.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.75  thf('105', plain,
% 0.54/0.75      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 0.54/0.75        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['103', '104'])).
% 0.54/0.75  thf('106', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['97', '98'])).
% 0.54/0.75  thf('107', plain,
% 0.54/0.75      (![X5 : $i, X6 : $i]:
% 0.54/0.75         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.54/0.75  thf('108', plain,
% 0.54/0.75      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['107'])).
% 0.54/0.75  thf('109', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf('110', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['97', '98'])).
% 0.54/0.75  thf('111', plain,
% 0.54/0.75      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['107'])).
% 0.54/0.75  thf('112', plain, (((k1_xboole_0) = (sk_D))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['105', '106', '108', '109', '110', '111'])).
% 0.54/0.75  thf('113', plain,
% 0.54/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.54/0.75         (((X25) != (k1_xboole_0))
% 0.54/0.75          | ((X26) = (k1_xboole_0))
% 0.54/0.75          | (v1_funct_2 @ X27 @ X26 @ X25)
% 0.54/0.75          | ((X27) != (k1_xboole_0))
% 0.54/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.75  thf('114', plain,
% 0.54/0.75      (![X26 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.54/0.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ k1_xboole_0)))
% 0.54/0.75          | (v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0)
% 0.54/0.75          | ((X26) = (k1_xboole_0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['113'])).
% 0.54/0.75  thf('115', plain,
% 0.54/0.75      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['107'])).
% 0.54/0.75  thf('116', plain,
% 0.54/0.75      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('117', plain,
% 0.54/0.75      (![X26 : $i]:
% 0.54/0.75         ((v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0)
% 0.54/0.75          | ((X26) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.54/0.75  thf('118', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['89', '90'])).
% 0.54/0.75  thf('119', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['97', '98'])).
% 0.54/0.75  thf('120', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0)),
% 0.54/0.75      inference('demod', [status(thm)], ['118', '119'])).
% 0.54/0.75  thf('121', plain, (((k1_xboole_0) = (sk_D))),
% 0.54/0.75      inference('demod', [status(thm)],
% 0.54/0.75                ['105', '106', '108', '109', '110', '111'])).
% 0.54/0.75  thf('122', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)),
% 0.54/0.75      inference('demod', [status(thm)], ['120', '121'])).
% 0.54/0.75  thf('123', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['117', '122'])).
% 0.54/0.75  thf('124', plain,
% 0.54/0.75      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['52', '57'])).
% 0.54/0.75  thf('125', plain, ($false),
% 0.54/0.75      inference('demod', [status(thm)], ['100', '112', '123', '124'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
