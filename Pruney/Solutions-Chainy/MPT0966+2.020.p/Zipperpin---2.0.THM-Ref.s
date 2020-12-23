%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IAXhzaLrTs

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:08 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  228 (1246 expanded)
%              Number of leaves         :   46 ( 376 expanded)
%              Depth                    :   27
%              Number of atoms          : 1471 (14968 expanded)
%              Number of equality atoms :  116 ( 950 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X40: $i,X41: $i] :
      ( m1_subset_1 @ ( sk_C @ X40 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( sk_C @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X40: $i,X41: $i] :
      ( v1_funct_2 @ ( sk_C @ X40 @ X41 ) @ X41 @ X40 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','21'])).

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

thf('23',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['23'])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['37','42'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X31 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['23'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['23'])).

thf('52',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['27','50','51'])).

thf('53',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['24','52'])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','53'])).

thf('55',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('56',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('59',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('60',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('67',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['65','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('75',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('78',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('92',plain,(
    ! [X40: $i,X41: $i] :
      ( v1_funct_2 @ ( sk_C @ X40 @ X41 ) @ X41 @ X40 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('94',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('95',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['84'])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('100',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('102',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['84'])).

thf('106',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['23'])).

thf('107',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ X0 @ k1_xboole_0 @ sk_C_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','108'])).

thf('110',plain,
    ( ~ ( v1_xboole_0 @ ( sk_C @ sk_C_1 @ k1_xboole_0 ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( sk_C @ sk_C_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','110'])).

thf('112',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('117',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('118',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['84'])).

thf('119',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['23'])).

thf('120',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['116','121'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['23'])).

thf('124',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['84'])).

thf('125',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['27','115','122','123','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['89','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['80','126'])).

thf('128',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('129',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['127','130'])).

thf('132',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['64','131'])).

thf('133',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['61','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('135',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('136',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('139',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('143',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('144',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['141','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('147',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['134','147'])).

thf('149',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['133','150'])).

thf('152',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['54','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('154',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('155',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('157',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('159',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('160',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('161',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('163',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('164',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['61','132'])).

thf('166',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('168',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['24','52'])).

thf('171',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,(
    ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['161','171'])).

thf('173',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['158','172'])).

thf('174',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('175',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('176',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['158','172'])).

thf('177',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('178',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['157','173','174','175','176','177'])).

thf('179',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('180',plain,(
    $false ),
    inference(demod,[status(thm)],['152','178','179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IAXhzaLrTs
% 0.16/0.36  % Computer   : n008.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 16:03:15 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.90/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.10  % Solved by: fo/fo7.sh
% 0.90/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.10  % done 1071 iterations in 0.627s
% 0.90/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.10  % SZS output start Refutation
% 0.90/1.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.10  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.10  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.10  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.10  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.10  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.90/1.10  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.10  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.90/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.10  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.90/1.10  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.10  thf(t7_xboole_0, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.90/1.10          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.90/1.10  thf('0', plain,
% 0.90/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.90/1.10      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.90/1.10  thf(d10_xboole_0, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.10  thf('1', plain,
% 0.90/1.10      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('2', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.90/1.10      inference('simplify', [status(thm)], ['1'])).
% 0.90/1.10  thf(t3_subset, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.10  thf('3', plain,
% 0.90/1.10      (![X8 : $i, X10 : $i]:
% 0.90/1.10         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.10  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf(t5_subset, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.90/1.10          ( v1_xboole_0 @ C ) ) ))).
% 0.90/1.10  thf('5', plain,
% 0.90/1.10      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.90/1.10         (~ (r2_hidden @ X11 @ X12)
% 0.90/1.10          | ~ (v1_xboole_0 @ X13)
% 0.90/1.10          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t5_subset])).
% 0.90/1.10  thf('6', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.10  thf('7', plain,
% 0.90/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['0', '6'])).
% 0.90/1.10  thf('8', plain,
% 0.90/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['0', '6'])).
% 0.90/1.10  thf('9', plain,
% 0.90/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.90/1.10      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.90/1.10  thf(t113_zfmisc_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.90/1.10       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.90/1.10  thf('10', plain,
% 0.90/1.10      (![X6 : $i, X7 : $i]:
% 0.90/1.10         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.90/1.10  thf('11', plain,
% 0.90/1.10      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['10'])).
% 0.90/1.10  thf(rc1_funct_2, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ?[C:$i]:
% 0.90/1.10       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 0.90/1.10         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 0.90/1.10         ( v1_relat_1 @ C ) & 
% 0.90/1.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.90/1.10  thf('12', plain,
% 0.90/1.10      (![X40 : $i, X41 : $i]:
% 0.90/1.10         (m1_subset_1 @ (sk_C @ X40 @ X41) @ 
% 0.90/1.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))),
% 0.90/1.10      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.90/1.10  thf('13', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (m1_subset_1 @ (sk_C @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.90/1.10      inference('sup+', [status(thm)], ['11', '12'])).
% 0.90/1.10  thf('14', plain,
% 0.90/1.10      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.90/1.10         (~ (r2_hidden @ X11 @ X12)
% 0.90/1.10          | ~ (v1_xboole_0 @ X13)
% 0.90/1.10          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t5_subset])).
% 0.90/1.10  thf('15', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.10          | ~ (r2_hidden @ X1 @ (sk_C @ X0 @ k1_xboole_0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.10  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.90/1.10  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.10  thf('17', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (sk_C @ X0 @ k1_xboole_0))),
% 0.90/1.10      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.10  thf('18', plain, (![X0 : $i]: ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['9', '17'])).
% 0.90/1.10  thf('19', plain,
% 0.90/1.10      (![X40 : $i, X41 : $i]: (v1_funct_2 @ (sk_C @ X40 @ X41) @ X41 @ X40)),
% 0.90/1.10      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.90/1.10  thf('20', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.90/1.10      inference('sup+', [status(thm)], ['18', '19'])).
% 0.90/1.10  thf('21', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup+', [status(thm)], ['8', '20'])).
% 0.90/1.10  thf('22', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         ((v1_funct_2 @ X2 @ X0 @ X1)
% 0.90/1.10          | ~ (v1_xboole_0 @ X0)
% 0.90/1.10          | ~ (v1_xboole_0 @ X2))),
% 0.90/1.10      inference('sup+', [status(thm)], ['7', '21'])).
% 0.90/1.10  thf(t8_funct_2, conjecture,
% 0.90/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.10     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.90/1.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.10       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.90/1.10         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.90/1.10           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.90/1.10             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.10    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.10        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.90/1.10            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.10          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.90/1.10            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.90/1.10              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.90/1.10                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.90/1.10    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.90/1.10  thf('23', plain,
% 0.90/1.10      ((~ (v1_funct_1 @ sk_D)
% 0.90/1.10        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.90/1.10        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('24', plain,
% 0.90/1.10      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.90/1.10         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.90/1.10      inference('split', [status(esa)], ['23'])).
% 0.90/1.10  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('26', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.90/1.10      inference('split', [status(esa)], ['23'])).
% 0.90/1.10  thf('27', plain, (((v1_funct_1 @ sk_D))),
% 0.90/1.10      inference('sup-', [status(thm)], ['25', '26'])).
% 0.90/1.10  thf('28', plain,
% 0.90/1.10      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('29', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(redefinition_k2_relset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.90/1.10  thf('30', plain,
% 0.90/1.10      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.90/1.10         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.90/1.10          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.90/1.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.10  thf('31', plain,
% 0.90/1.10      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.90/1.10      inference('sup-', [status(thm)], ['29', '30'])).
% 0.90/1.10  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.90/1.10      inference('demod', [status(thm)], ['28', '31'])).
% 0.90/1.10  thf('33', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(cc2_relset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.90/1.10  thf('34', plain,
% 0.90/1.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.90/1.10         ((v4_relat_1 @ X20 @ X21)
% 0.90/1.10          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.90/1.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.90/1.10  thf('35', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.90/1.10      inference('sup-', [status(thm)], ['33', '34'])).
% 0.90/1.10  thf(d18_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ B ) =>
% 0.90/1.10       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.90/1.10  thf('36', plain,
% 0.90/1.10      (![X16 : $i, X17 : $i]:
% 0.90/1.10         (~ (v4_relat_1 @ X16 @ X17)
% 0.90/1.10          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.90/1.10          | ~ (v1_relat_1 @ X16))),
% 0.90/1.10      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.90/1.10  thf('37', plain,
% 0.90/1.10      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['35', '36'])).
% 0.90/1.10  thf('38', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(cc2_relat_1, axiom,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ A ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.90/1.10  thf('39', plain,
% 0.90/1.10      (![X14 : $i, X15 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.90/1.10          | (v1_relat_1 @ X14)
% 0.90/1.10          | ~ (v1_relat_1 @ X15))),
% 0.90/1.10      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.90/1.10  thf('40', plain,
% 0.90/1.10      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.90/1.10      inference('sup-', [status(thm)], ['38', '39'])).
% 0.90/1.10  thf(fc6_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.90/1.10  thf('41', plain,
% 0.90/1.10      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.90/1.10      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.10  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.10      inference('demod', [status(thm)], ['40', '41'])).
% 0.90/1.10  thf('43', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.90/1.10      inference('demod', [status(thm)], ['37', '42'])).
% 0.90/1.10  thf(t11_relset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ C ) =>
% 0.90/1.10       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.90/1.10           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.90/1.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.90/1.10  thf('44', plain,
% 0.90/1.10      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.90/1.10         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.90/1.10          | ~ (r1_tarski @ (k2_relat_1 @ X29) @ X31)
% 0.90/1.10          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.90/1.10          | ~ (v1_relat_1 @ X29))),
% 0.90/1.10      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.90/1.10  thf('45', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ sk_D)
% 0.90/1.10          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.10          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.10  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.10      inference('demod', [status(thm)], ['40', '41'])).
% 0.90/1.10  thf('47', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.10          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.90/1.10      inference('demod', [status(thm)], ['45', '46'])).
% 0.90/1.10  thf('48', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['32', '47'])).
% 0.90/1.10  thf('49', plain,
% 0.90/1.10      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.90/1.10         <= (~
% 0.90/1.10             ((m1_subset_1 @ sk_D @ 
% 0.90/1.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.90/1.10      inference('split', [status(esa)], ['23'])).
% 0.90/1.10  thf('50', plain,
% 0.90/1.10      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['48', '49'])).
% 0.90/1.10  thf('51', plain,
% 0.90/1.10      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 0.90/1.10       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.90/1.10       ~ ((v1_funct_1 @ sk_D))),
% 0.90/1.10      inference('split', [status(esa)], ['23'])).
% 0.90/1.10  thf('52', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.90/1.10      inference('sat_resolution*', [status(thm)], ['27', '50', '51'])).
% 0.90/1.10  thf('53', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.90/1.10      inference('simpl_trail', [status(thm)], ['24', '52'])).
% 0.90/1.10  thf('54', plain, ((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['22', '53'])).
% 0.90/1.10  thf('55', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(d1_funct_2, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.10           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.90/1.10             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.90/1.10         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.10           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.90/1.10             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_1, axiom,
% 0.90/1.10    (![C:$i,B:$i,A:$i]:
% 0.90/1.10     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.90/1.10       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.90/1.10  thf('56', plain,
% 0.90/1.10      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.10         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.90/1.10          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.90/1.10          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.10  thf('57', plain,
% 0.90/1.10      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.90/1.10        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['55', '56'])).
% 0.90/1.10  thf('58', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.10  thf('59', plain,
% 0.90/1.10      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.90/1.10         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.90/1.10          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.90/1.10      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.10  thf('60', plain,
% 0.90/1.10      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.90/1.10      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.10  thf('61', plain,
% 0.90/1.10      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.90/1.10        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.90/1.10      inference('demod', [status(thm)], ['57', '60'])).
% 0.90/1.10  thf('62', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.90/1.10  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.90/1.10  thf(zf_stmt_4, axiom,
% 0.90/1.10    (![B:$i,A:$i]:
% 0.90/1.10     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.10       ( zip_tseitin_0 @ B @ A ) ))).
% 0.90/1.10  thf(zf_stmt_5, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.90/1.10         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.10           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.90/1.10             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.90/1.10  thf('63', plain,
% 0.90/1.10      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.10         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.90/1.10          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.90/1.10          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.10  thf('64', plain,
% 0.90/1.10      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.90/1.10        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['62', '63'])).
% 0.90/1.10  thf('65', plain,
% 0.90/1.10      (![X32 : $i, X33 : $i]:
% 0.90/1.10         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.90/1.10  thf('66', plain,
% 0.90/1.10      (![X6 : $i, X7 : $i]:
% 0.90/1.10         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.90/1.10  thf('67', plain,
% 0.90/1.10      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['66'])).
% 0.90/1.10  thf('68', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.10         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.90/1.10      inference('sup+', [status(thm)], ['65', '67'])).
% 0.90/1.10  thf('69', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('70', plain,
% 0.90/1.10      (![X8 : $i, X9 : $i]:
% 0.90/1.10         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.10  thf('71', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.10  thf('72', plain,
% 0.90/1.10      (![X1 : $i, X3 : $i]:
% 0.90/1.10         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('73', plain,
% 0.90/1.10      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_D)
% 0.90/1.10        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['71', '72'])).
% 0.90/1.10  thf('74', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 0.90/1.10          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 0.90/1.10          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['68', '73'])).
% 0.90/1.10  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.90/1.10  thf('75', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.90/1.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.90/1.10  thf('76', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 0.90/1.10          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 0.90/1.10      inference('demod', [status(thm)], ['74', '75'])).
% 0.90/1.10  thf('77', plain,
% 0.90/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['0', '6'])).
% 0.90/1.10  thf('78', plain,
% 0.90/1.10      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['66'])).
% 0.90/1.10  thf('79', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup+', [status(thm)], ['77', '78'])).
% 0.90/1.10  thf('80', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (((sk_D) = (k1_xboole_0))
% 0.90/1.10          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 0.90/1.10          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.90/1.10      inference('sup+', [status(thm)], ['76', '79'])).
% 0.90/1.10  thf('81', plain,
% 0.90/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['0', '6'])).
% 0.90/1.10  thf('82', plain,
% 0.90/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['0', '6'])).
% 0.90/1.10  thf('83', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]:
% 0.90/1.10         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.10      inference('sup+', [status(thm)], ['81', '82'])).
% 0.90/1.10  thf('84', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('85', plain,
% 0.90/1.10      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.90/1.10      inference('split', [status(esa)], ['84'])).
% 0.90/1.10  thf('86', plain,
% 0.90/1.10      ((![X0 : $i]:
% 0.90/1.10          (((X0) != (k1_xboole_0))
% 0.90/1.10           | ~ (v1_xboole_0 @ X0)
% 0.90/1.10           | ~ (v1_xboole_0 @ sk_B_1)))
% 0.90/1.10         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['83', '85'])).
% 0.90/1.10  thf('87', plain,
% 0.90/1.10      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.90/1.10         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.90/1.10      inference('simplify', [status(thm)], ['86'])).
% 0.90/1.10  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.10  thf('89', plain,
% 0.90/1.10      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.90/1.10      inference('simplify_reflect+', [status(thm)], ['87', '88'])).
% 0.90/1.10  thf('90', plain, (![X0 : $i]: ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['9', '17'])).
% 0.90/1.10  thf('91', plain,
% 0.90/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['0', '6'])).
% 0.90/1.10  thf('92', plain,
% 0.90/1.10      (![X40 : $i, X41 : $i]: (v1_funct_2 @ (sk_C @ X40 @ X41) @ X41 @ X40)),
% 0.90/1.10      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.90/1.10  thf('93', plain,
% 0.90/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['0', '6'])).
% 0.90/1.10  thf('94', plain,
% 0.90/1.10      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['10'])).
% 0.90/1.10  thf('95', plain,
% 0.90/1.10      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('split', [status(esa)], ['84'])).
% 0.90/1.10  thf('96', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('97', plain,
% 0.90/1.10      (((m1_subset_1 @ sk_D @ 
% 0.90/1.10         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.90/1.10         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup+', [status(thm)], ['95', '96'])).
% 0.90/1.10  thf('98', plain,
% 0.90/1.10      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.90/1.10         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup+', [status(thm)], ['94', '97'])).
% 0.90/1.10  thf('99', plain,
% 0.90/1.10      (![X8 : $i, X9 : $i]:
% 0.90/1.10         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.10  thf('100', plain,
% 0.90/1.10      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['98', '99'])).
% 0.90/1.10  thf('101', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.90/1.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.90/1.10  thf('102', plain,
% 0.90/1.10      (![X1 : $i, X3 : $i]:
% 0.90/1.10         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('103', plain,
% 0.90/1.10      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['101', '102'])).
% 0.90/1.10  thf('104', plain,
% 0.90/1.10      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['100', '103'])).
% 0.90/1.10  thf('105', plain,
% 0.90/1.10      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('split', [status(esa)], ['84'])).
% 0.90/1.10  thf('106', plain,
% 0.90/1.10      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.90/1.10         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.90/1.10      inference('split', [status(esa)], ['23'])).
% 0.90/1.10  thf('107', plain,
% 0.90/1.10      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.90/1.10         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.90/1.10             (((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['105', '106'])).
% 0.90/1.10  thf('108', plain,
% 0.90/1.10      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 0.90/1.10         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.90/1.10             (((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['104', '107'])).
% 0.90/1.10  thf('109', plain,
% 0.90/1.10      ((![X0 : $i]:
% 0.90/1.10          (~ (v1_funct_2 @ X0 @ k1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ X0)))
% 0.90/1.10         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.90/1.10             (((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['93', '108'])).
% 0.90/1.10  thf('110', plain,
% 0.90/1.10      ((~ (v1_xboole_0 @ (sk_C @ sk_C_1 @ k1_xboole_0)))
% 0.90/1.10         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.90/1.10             (((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['92', '109'])).
% 0.90/1.10  thf('111', plain,
% 0.90/1.10      ((![X0 : $i]:
% 0.90/1.10          (~ (v1_xboole_0 @ (sk_C @ sk_C_1 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.90/1.10         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.90/1.10             (((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['91', '110'])).
% 0.90/1.10  thf('112', plain,
% 0.90/1.10      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.90/1.10         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.90/1.10             (((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['90', '111'])).
% 0.90/1.10  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.10  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.10  thf('115', plain,
% 0.90/1.10      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.90/1.10      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.90/1.10  thf('116', plain,
% 0.90/1.10      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.90/1.10         <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup+', [status(thm)], ['94', '97'])).
% 0.90/1.10  thf('117', plain,
% 0.90/1.10      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['10'])).
% 0.90/1.10  thf('118', plain,
% 0.90/1.10      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('split', [status(esa)], ['84'])).
% 0.90/1.10  thf('119', plain,
% 0.90/1.10      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.90/1.10         <= (~
% 0.90/1.10             ((m1_subset_1 @ sk_D @ 
% 0.90/1.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.90/1.10      inference('split', [status(esa)], ['23'])).
% 0.90/1.10  thf('120', plain,
% 0.90/1.10      ((~ (m1_subset_1 @ sk_D @ 
% 0.90/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.90/1.10         <= (~
% 0.90/1.10             ((m1_subset_1 @ sk_D @ 
% 0.90/1.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.90/1.10             (((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['118', '119'])).
% 0.90/1.10  thf('121', plain,
% 0.90/1.10      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.90/1.10         <= (~
% 0.90/1.10             ((m1_subset_1 @ sk_D @ 
% 0.90/1.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.90/1.10             (((sk_A) = (k1_xboole_0))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['117', '120'])).
% 0.90/1.10  thf('122', plain,
% 0.90/1.10      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.90/1.10       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['116', '121'])).
% 0.90/1.10  thf('123', plain,
% 0.90/1.10      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.90/1.10       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 0.90/1.10      inference('split', [status(esa)], ['23'])).
% 0.90/1.10  thf('124', plain,
% 0.90/1.10      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.90/1.10      inference('split', [status(esa)], ['84'])).
% 0.90/1.10  thf('125', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.90/1.10      inference('sat_resolution*', [status(thm)],
% 0.90/1.10                ['27', '115', '122', '123', '124'])).
% 0.90/1.10  thf('126', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.90/1.10      inference('simpl_trail', [status(thm)], ['89', '125'])).
% 0.90/1.10  thf('127', plain,
% 0.90/1.10      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 0.90/1.10      inference('clc', [status(thm)], ['80', '126'])).
% 0.90/1.10  thf('128', plain,
% 0.90/1.10      (![X32 : $i, X33 : $i]:
% 0.90/1.10         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.90/1.10  thf('129', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.10  thf('130', plain,
% 0.90/1.10      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.90/1.10      inference('sup+', [status(thm)], ['128', '129'])).
% 0.90/1.10  thf('131', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.90/1.10      inference('clc', [status(thm)], ['127', '130'])).
% 0.90/1.10  thf('132', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.90/1.10      inference('demod', [status(thm)], ['64', '131'])).
% 0.90/1.10  thf('133', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.90/1.10      inference('demod', [status(thm)], ['61', '132'])).
% 0.90/1.10  thf('134', plain,
% 0.90/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['0', '6'])).
% 0.90/1.10  thf('135', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.90/1.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.90/1.10  thf('136', plain,
% 0.90/1.10      (![X8 : $i, X10 : $i]:
% 0.90/1.10         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.10  thf('137', plain,
% 0.90/1.10      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['135', '136'])).
% 0.90/1.10  thf('138', plain,
% 0.90/1.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.90/1.10         ((v4_relat_1 @ X20 @ X21)
% 0.90/1.10          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.90/1.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.90/1.10  thf('139', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['137', '138'])).
% 0.90/1.10  thf('140', plain,
% 0.90/1.10      (![X16 : $i, X17 : $i]:
% 0.90/1.10         (~ (v4_relat_1 @ X16 @ X17)
% 0.90/1.10          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.90/1.10          | ~ (v1_relat_1 @ X16))),
% 0.90/1.10      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.90/1.10  thf('141', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         (~ (v1_relat_1 @ k1_xboole_0)
% 0.90/1.10          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['139', '140'])).
% 0.90/1.10  thf('142', plain,
% 0.90/1.10      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['10'])).
% 0.90/1.10  thf('143', plain,
% 0.90/1.10      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 0.90/1.10      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.10  thf('144', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.90/1.10      inference('sup+', [status(thm)], ['142', '143'])).
% 0.90/1.10  thf('145', plain,
% 0.90/1.10      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.90/1.10      inference('demod', [status(thm)], ['141', '144'])).
% 0.90/1.10  thf('146', plain,
% 0.90/1.10      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['101', '102'])).
% 0.90/1.10  thf('147', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['145', '146'])).
% 0.90/1.10  thf('148', plain,
% 0.90/1.10      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup+', [status(thm)], ['134', '147'])).
% 0.90/1.10  thf('149', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.10  thf('150', plain,
% 0.90/1.10      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.10      inference('sup+', [status(thm)], ['148', '149'])).
% 0.90/1.10  thf('151', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 0.90/1.10      inference('sup+', [status(thm)], ['133', '150'])).
% 0.90/1.10  thf('152', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.90/1.10      inference('clc', [status(thm)], ['54', '151'])).
% 0.90/1.10  thf('153', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['32', '47'])).
% 0.90/1.10  thf('154', plain,
% 0.90/1.10      (![X8 : $i, X9 : $i]:
% 0.90/1.10         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.90/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.10  thf('155', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['153', '154'])).
% 0.90/1.10  thf('156', plain,
% 0.90/1.10      (![X1 : $i, X3 : $i]:
% 0.90/1.10         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.90/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.10  thf('157', plain,
% 0.90/1.10      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ sk_D)
% 0.90/1.10        | ((k2_zfmisc_1 @ sk_A @ sk_C_1) = (sk_D)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['155', '156'])).
% 0.90/1.10  thf('158', plain,
% 0.90/1.10      (![X32 : $i, X33 : $i]:
% 0.90/1.10         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.90/1.10  thf('159', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['32', '47'])).
% 0.90/1.10  thf('160', plain,
% 0.90/1.10      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.10         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.90/1.10          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.90/1.10          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.10  thf('161', plain,
% 0.90/1.10      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.90/1.10        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 0.90/1.10      inference('sup-', [status(thm)], ['159', '160'])).
% 0.90/1.10  thf('162', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['32', '47'])).
% 0.90/1.10  thf('163', plain,
% 0.90/1.10      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.90/1.10         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.90/1.10          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.90/1.10      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.10  thf('164', plain,
% 0.90/1.10      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.90/1.10      inference('sup-', [status(thm)], ['162', '163'])).
% 0.90/1.10  thf('165', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.90/1.10      inference('demod', [status(thm)], ['61', '132'])).
% 0.90/1.10  thf('166', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 0.90/1.10      inference('demod', [status(thm)], ['164', '165'])).
% 0.90/1.10  thf('167', plain,
% 0.90/1.10      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.10         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 0.90/1.10          | (v1_funct_2 @ X36 @ X34 @ X35)
% 0.90/1.10          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.10  thf('168', plain,
% 0.90/1.10      ((((sk_A) != (sk_A))
% 0.90/1.10        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.90/1.10        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['166', '167'])).
% 0.90/1.10  thf('169', plain,
% 0.90/1.10      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.90/1.10        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 0.90/1.10      inference('simplify', [status(thm)], ['168'])).
% 0.90/1.10  thf('170', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.90/1.10      inference('simpl_trail', [status(thm)], ['24', '52'])).
% 0.90/1.10  thf('171', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 0.90/1.10      inference('clc', [status(thm)], ['169', '170'])).
% 0.90/1.10  thf('172', plain, (~ (zip_tseitin_0 @ sk_C_1 @ sk_A)),
% 0.90/1.10      inference('clc', [status(thm)], ['161', '171'])).
% 0.90/1.10  thf('173', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['158', '172'])).
% 0.90/1.10  thf('174', plain,
% 0.90/1.10      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['66'])).
% 0.90/1.10  thf('175', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.90/1.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.90/1.10  thf('176', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['158', '172'])).
% 0.90/1.10  thf('177', plain,
% 0.90/1.10      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.10      inference('simplify', [status(thm)], ['66'])).
% 0.90/1.10  thf('178', plain, (((k1_xboole_0) = (sk_D))),
% 0.90/1.10      inference('demod', [status(thm)],
% 0.90/1.10                ['157', '173', '174', '175', '176', '177'])).
% 0.90/1.10  thf('179', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.10  thf('180', plain, ($false),
% 0.90/1.10      inference('demod', [status(thm)], ['152', '178', '179'])).
% 0.90/1.10  
% 0.90/1.10  % SZS output end Refutation
% 0.90/1.10  
% 0.90/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
