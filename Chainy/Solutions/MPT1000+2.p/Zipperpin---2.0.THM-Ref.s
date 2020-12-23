%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1000+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AwA3nfqdxS

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 53.28s
% Output     : Refutation 53.28s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 220 expanded)
%              Number of leaves         :   33 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  637 (2061 expanded)
%              Number of equality atoms :  103 ( 303 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_97_type,type,(
    zip_tseitin_97: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_98_type,type,(
    sk_B_98: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_110_type,type,(
    sk_C_110: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_98_type,type,(
    zip_tseitin_98: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
          <=> ( A
              = ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_97 @ ( B @ A ) ) ) )).

thf('0',plain,(
    ! [X4642: $i,X4643: $i] :
      ( ( zip_tseitin_97 @ ( X4642 @ X4643 ) )
      | ( X4642 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ! [X4642: $i,X4643: $i] :
      ( ( zip_tseitin_97 @ ( X4642 @ X4643 ) )
      | ( X4642 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
        & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ ( A @ ( B @ ( C @ B ) ) ) )
          = A ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
          & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k8_relset_1 @ ( A @ ( B @ ( C @ B ) ) ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_funct_2])).

thf('3',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_98: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_98 @ ( C @ ( B @ A ) ) )
     => ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
      <=> ( A
          = ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_97: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( zip_tseitin_97 @ ( B @ A ) )
         => ( zip_tseitin_98 @ ( C @ ( B @ A ) ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X4647: $i,X4648: $i,X4649: $i] :
      ( ~ ( zip_tseitin_97 @ ( X4647 @ X4648 ) )
      | ( zip_tseitin_98 @ ( X4649 @ ( X4647 @ X4648 ) ) )
      | ~ ( m1_subset_1 @ ( X4649 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X4648 @ X4647 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,
    ( ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_98 @ sk_A_16 ) ) )
    | ~ ( zip_tseitin_97 @ ( sk_B_98 @ sk_A_16 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_98 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X4644: $i,X4645: $i,X4646: $i] :
      ( ~ ( v1_funct_2 @ ( X4646 @ ( X4644 @ X4645 ) ) )
      | ( X4644
        = ( k1_relset_1 @ ( X4644 @ ( X4645 @ X4646 ) ) ) )
      | ~ ( zip_tseitin_98 @ ( X4646 @ ( X4645 @ X4644 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,
    ( ~ ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_98 @ sk_A_16 ) ) )
    | ( sk_A_16
      = ( k1_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X3595: $i,X3596: $i,X3597: $i] :
      ( ( ( k1_relset_1 @ ( X3596 @ ( X3597 @ X3595 ) ) )
        = ( k1_relat_1 @ X3595 ) )
      | ~ ( m1_subset_1 @ ( X3595 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3596 @ X3597 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) )
    = ( k1_relat_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_98 @ sk_A_16 ) ) )
    | ( sk_A_16
      = ( k1_relat_1 @ sk_C_110 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ( k8_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ ( sk_C_110 @ sk_B_98 ) ) ) )
 != sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( k7_relset_1 @ ( A @ ( B @ ( C @ A ) ) ) )
          = ( k2_relset_1 @ ( A @ ( B @ C ) ) ) )
        & ( ( k8_relset_1 @ ( A @ ( B @ ( C @ B ) ) ) )
          = ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X3707: $i,X3708: $i,X3709: $i] :
      ( ( ( k8_relset_1 @ ( X3707 @ ( X3708 @ ( X3709 @ X3708 ) ) ) )
        = ( k1_relset_1 @ ( X3707 @ ( X3708 @ X3709 ) ) ) )
      | ~ ( m1_subset_1 @ ( X3709 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3707 @ X3708 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('16',plain,
    ( ( k8_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ ( sk_C_110 @ sk_B_98 ) ) ) )
    = ( k1_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ sk_C_110 ) ) )
    = ( k1_relat_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('18',plain,
    ( ( k8_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ ( sk_C_110 @ sk_B_98 ) ) ) )
    = ( k1_relat_1 @ sk_C_110 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ( k1_relat_1 @ sk_C_110 )
 != sk_A_16 ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ~ ( zip_tseitin_98 @ ( sk_C_110 @ ( sk_B_98 @ sk_A_16 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','19'])).

thf('21',plain,(
    ~ ( zip_tseitin_97 @ ( sk_B_98 @ sk_A_16 ) ) ),
    inference(clc,[status(thm)],['5','20'])).

thf('22',plain,(
    sk_B_98 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,
    ( ( sk_A_16 = k1_xboole_0 )
    | ( sk_B_98 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ( sk_B_98 != k1_xboole_0 )
   <= ( sk_B_98 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,
    ( ( sk_B_98 != o_0_0_xboole_0 )
   <= ( sk_B_98 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A_16 = k1_xboole_0 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('28',plain,
    ( ( k8_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ ( sk_C_110 @ sk_B_98 ) ) ) )
    = ( k1_relat_1 @ sk_C_110 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('29',plain,
    ( ( ( k8_relset_1 @ ( k1_xboole_0 @ ( sk_B_98 @ ( sk_C_110 @ sk_B_98 ) ) ) )
      = ( k1_relat_1 @ sk_C_110 ) )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('31',plain,
    ( ( sk_A_16 = k1_xboole_0 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('32',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_98 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_xboole_0 @ sk_B_98 ) ) ) ) )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ sk_B_98 ) ) ) ) )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('36',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1965 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,
    ( ( r1_tarski @ ( sk_C_110 @ ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ sk_B_98 ) ) ) )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X1104: $i,X1105: $i] :
      ( ( ( k2_zfmisc_1 @ ( X1104 @ X1105 ) )
        = k1_xboole_0 )
      | ( X1104 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( k1_xboole_0 @ X1105 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('41',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('42',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ X1105 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( sk_C_110 @ o_0_0_xboole_0 ) )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ ( A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X245: $i] :
      ( ( X245 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('45',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('46',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('47',plain,(
    ! [X245: $i] :
      ( ( X245 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( sk_C_110 = o_0_0_xboole_0 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,
    ( ( sk_C_110 = o_0_0_xboole_0 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('50',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('51',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('52',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('53',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ( k8_relset_1 @ ( o_0_0_xboole_0 @ ( sk_B_98 @ ( o_0_0_xboole_0 @ sk_B_98 ) ) ) )
      = o_0_0_xboole_0 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','48','49','53'])).

thf('55',plain,
    ( ( sk_A_16 = k1_xboole_0 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('56',plain,(
    ( k8_relset_1 @ ( sk_A_16 @ ( sk_B_98 @ ( sk_C_110 @ sk_B_98 ) ) ) )
 != sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,
    ( ( ( k8_relset_1 @ ( k1_xboole_0 @ ( sk_B_98 @ ( sk_C_110 @ sk_B_98 ) ) ) )
     != sk_A_16 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('59',plain,
    ( ( sk_A_16 = k1_xboole_0 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('60',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('61',plain,
    ( ( ( k8_relset_1 @ ( o_0_0_xboole_0 @ ( sk_B_98 @ ( sk_C_110 @ sk_B_98 ) ) ) )
     != o_0_0_xboole_0 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( sk_C_110 = o_0_0_xboole_0 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('63',plain,
    ( ( ( k8_relset_1 @ ( o_0_0_xboole_0 @ ( sk_B_98 @ ( o_0_0_xboole_0 @ sk_B_98 ) ) ) )
     != o_0_0_xboole_0 )
   <= ( sk_A_16 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    sk_A_16 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','63'])).

thf('65',plain,
    ( ( sk_B_98 != k1_xboole_0 )
    | ( sk_A_16 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('66',plain,(
    sk_B_98 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B_98 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['26','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','67'])).

%------------------------------------------------------------------------------
