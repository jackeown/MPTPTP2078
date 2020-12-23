%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0967+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SP2Cm0GWcS

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:47 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  189 (1793 expanded)
%              Number of leaves         :   35 ( 488 expanded)
%              Depth                    :   26
%              Number of atoms          : 1366 (26710 expanded)
%              Number of equality atoms :  126 (2152 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(zf_stmt_0,negated_conjecture,(
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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('10',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('12',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( zip_tseitin_0 @ X5 @ X6 )
      | ( zip_tseitin_1 @ X7 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_funct_2 @ X4 @ X2 @ X3 )
      | ( X2
        = ( k1_relset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( zip_tseitin_1 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('25',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('30',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('32',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_A )
      | ( sk_B_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ( r1_tarski @ sk_A @ sk_A ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( ( r1_tarski @ sk_A @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('41',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_funct_2 @ X4 @ X2 @ X3 )
      | ( X2
        = ( k1_relset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( zip_tseitin_1 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( zip_tseitin_0 @ X5 @ X6 )
      | ( zip_tseitin_1 @ X7 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','56'])).

thf('58',plain,
    ( ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','58'])).

thf('60',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,
    ( ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t17_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ) )).

thf('64',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X17 ) ) )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t17_relset_1])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
        | ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ~ ( r1_tarski @ k1_xboole_0 @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
        | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('69',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('71',plain,
    ( ( k1_xboole_0
      = ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','57'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k1_relset_1 @ X0 @ sk_B_1 @ sk_D ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('74',plain,
    ( ( ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('77',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_C @ sk_D )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X2
       != ( k1_relset_1 @ X2 @ X3 @ X4 ) )
      | ( v1_funct_2 @ X4 @ X2 @ X3 )
      | ~ ( zip_tseitin_1 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('80',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('82',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( zip_tseitin_0 @ X5 @ X6 )
      | ( zip_tseitin_1 @ X7 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('83',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('85',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','85'])).

thf('87',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('89',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('94',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('99',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','91','96','97','98'])).

thf('100',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(simpl_trail,[status(thm)],['41','99'])).

thf('101',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X17 ) ) )
      | ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t17_relset_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('110',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','108','109'])).

thf('111',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('113',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('114',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('116',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('117',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','91','96','97','98'])).

thf('118',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('122',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['114','122'])).

thf('124',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X2
       != ( k1_relset_1 @ X2 @ X3 @ X4 ) )
      | ( v1_funct_2 @ X4 @ X2 @ X3 )
      | ~ ( zip_tseitin_1 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('125',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('128',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( zip_tseitin_0 @ X5 @ X6 )
      | ( zip_tseitin_1 @ X7 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('129',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('130',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( sk_B @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('131',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('134',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('136',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('137',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_B_1 = X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('144',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ( zip_tseitin_0 @ sk_C @ X1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ sk_C @ X1 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('147',plain,
    ( ! [X1: $i] :
        ( zip_tseitin_0 @ sk_C @ X1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['145','146'])).

thf('148',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','91','96','97','98'])).

thf('149',plain,(
    ! [X1: $i] :
      ( zip_tseitin_0 @ sk_C @ X1 ) ),
    inference(simpl_trail,[status(thm)],['147','148'])).

thf('150',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['129','149'])).

thf('151',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['126','150'])).

thf('152',plain,(
    $false ),
    inference(demod,[status(thm)],['111','151'])).


%------------------------------------------------------------------------------
