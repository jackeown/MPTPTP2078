%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hc36DgPcV7

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:16 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 280 expanded)
%              Number of leaves         :   40 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  694 (3289 expanded)
%              Number of equality atoms :   38 ( 143 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k9_relat_1 @ X8 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X8 @ X6 @ X7 ) @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['9','12'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('17',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

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

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X16 ) ) )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( v1_xboole_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
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

thf('27',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['9','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['37','40'])).

thf('42',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','41'])).

thf('43',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('45',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k9_relat_1 @ X8 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X6 @ X7 ) @ X6 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('50',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('52',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['37','40'])).

thf('54',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['37','40'])).

thf('55',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X33: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hc36DgPcV7
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 173 iterations in 0.226s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.68  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.68  thf(t190_funct_2, conjecture,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.45/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.68       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.45/0.68            ( ![E:$i]:
% 0.45/0.68              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.45/0.68            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.68          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.45/0.68               ( ![E:$i]:
% 0.45/0.68                 ( ( m1_subset_1 @ E @ B ) =>
% 0.45/0.68                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.45/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.68  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.45/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.68  thf(t146_relat_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ A ) =>
% 0.45/0.68       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      (![X9 : $i]:
% 0.45/0.68         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 0.45/0.68          | ~ (v1_relat_1 @ X9))),
% 0.45/0.68      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.45/0.68  thf(t143_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ C ) =>
% 0.45/0.68       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.45/0.68         ( ?[D:$i]:
% 0.45/0.68           ( ( r2_hidden @ D @ B ) & 
% 0.45/0.68             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.45/0.68             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X7 @ (k9_relat_1 @ X8 @ X6))
% 0.45/0.68          | (r2_hidden @ (k4_tarski @ (sk_D @ X8 @ X6 @ X7) @ X7) @ X8)
% 0.45/0.68          | ~ (v1_relat_1 @ X8))),
% 0.45/0.68      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | (r2_hidden @ 
% 0.45/0.68             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((r2_hidden @ 
% 0.45/0.68           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.68        | (r2_hidden @ 
% 0.45/0.68           (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.45/0.68           sk_D_1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['4', '8'])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(cc1_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( v1_relat_1 @ C ) ))).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.68         ((v1_relat_1 @ X13)
% 0.45/0.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.68  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      ((r2_hidden @ 
% 0.45/0.68        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.45/0.68        sk_D_1)),
% 0.45/0.68      inference('demod', [status(thm)], ['9', '12'])).
% 0.45/0.68  thf(t8_funct_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.68       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.45/0.68         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.45/0.68           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.68         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.45/0.68          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.45/0.68          | ~ (v1_funct_1 @ X11)
% 0.45/0.68          | ~ (v1_relat_1 @ X11))),
% 0.45/0.68      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.68        | ((sk_A)
% 0.45/0.68            = (k1_funct_1 @ sk_D_1 @ 
% 0.45/0.68               (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf('17', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (((sk_A)
% 0.45/0.68         = (k1_funct_1 @ sk_D_1 @ 
% 0.45/0.68            (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.45/0.68  thf(d1_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_1, axiom,
% 0.45/0.68    (![B:$i,A:$i]:
% 0.45/0.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.68       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.68  thf('19', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i]:
% 0.45/0.68         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.68  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.68  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.45/0.68      inference('sup+', [status(thm)], ['19', '20'])).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(cc4_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( v1_xboole_0 @ A ) =>
% 0.45/0.68       ( ![C:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.45/0.68           ( v1_xboole_0 @ C ) ) ) ))).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.68         (~ (v1_xboole_0 @ X16)
% 0.45/0.68          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X16)))
% 0.45/0.68          | (v1_xboole_0 @ X17))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.45/0.68  thf('24', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.68  thf('25', plain,
% 0.45/0.68      (![X0 : $i]: ((zip_tseitin_0 @ sk_C @ X0) | (v1_xboole_0 @ sk_D_1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['21', '24'])).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.68  thf(zf_stmt_3, axiom,
% 0.45/0.68    (![C:$i,B:$i,A:$i]:
% 0.45/0.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.68  thf(zf_stmt_5, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.68  thf('27', plain,
% 0.45/0.68      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.68         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.45/0.68          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.45/0.68          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.45/0.68        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      (((v1_xboole_0 @ sk_D_1) | (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['25', '28'])).
% 0.45/0.68  thf('30', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.68         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.45/0.68          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.45/0.68          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.45/0.68        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.68         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.45/0.68          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (((k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.68  thf('36', plain,
% 0.45/0.68      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.45/0.68        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.68      inference('demod', [status(thm)], ['32', '35'])).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (((v1_xboole_0 @ sk_D_1) | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['29', '36'])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      ((r2_hidden @ 
% 0.45/0.68        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.45/0.68        sk_D_1)),
% 0.45/0.68      inference('demod', [status(thm)], ['9', '12'])).
% 0.45/0.68  thf(d1_xboole_0, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.68  thf('39', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.68  thf('40', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.45/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.68  thf('41', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.68      inference('clc', [status(thm)], ['37', '40'])).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      (((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['18', '41'])).
% 0.45/0.68  thf('43', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.45/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      (![X9 : $i]:
% 0.45/0.68         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 0.45/0.68          | ~ (v1_relat_1 @ X9))),
% 0.45/0.68      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.45/0.68  thf('45', plain,
% 0.45/0.68      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X7 @ (k9_relat_1 @ X8 @ X6))
% 0.45/0.68          | (r2_hidden @ (sk_D @ X8 @ X6 @ X7) @ X6)
% 0.45/0.68          | ~ (v1_relat_1 @ X8))),
% 0.45/0.68      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.68  thf('46', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.45/0.68             (k1_relat_1 @ X0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ (k1_relat_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.68  thf('48', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.68        | (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.45/0.68           (k1_relat_1 @ sk_D_1)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['43', '47'])).
% 0.45/0.68  thf('49', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf('50', plain,
% 0.45/0.68      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.45/0.68        (k1_relat_1 @ sk_D_1))),
% 0.45/0.68      inference('demod', [status(thm)], ['48', '49'])).
% 0.45/0.68  thf(t1_subset, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.68  thf('51', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.68  thf('52', plain,
% 0.45/0.68      ((m1_subset_1 @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.45/0.68        (k1_relat_1 @ sk_D_1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.68  thf('53', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.68      inference('clc', [status(thm)], ['37', '40'])).
% 0.45/0.68  thf('54', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.68      inference('clc', [status(thm)], ['37', '40'])).
% 0.45/0.68  thf('55', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.45/0.68      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.45/0.68  thf('56', plain,
% 0.45/0.68      (![X33 : $i]:
% 0.45/0.68         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X33))
% 0.45/0.68          | ~ (m1_subset_1 @ X33 @ sk_B_1))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('57', plain,
% 0.45/0.68      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.68  thf('58', plain, ($false),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)], ['42', '57'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
