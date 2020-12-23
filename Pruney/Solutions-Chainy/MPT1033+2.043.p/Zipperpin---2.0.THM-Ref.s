%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1xLIIhJCaL

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 321 expanded)
%              Number of leaves         :   26 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :  705 (4796 expanded)
%              Number of equality atoms :   63 ( 374 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X21 = X18 )
      | ~ ( r1_partfun1 @ X21 @ X18 )
      | ~ ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_partfun1 @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('12',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_B_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('19',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('21',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','28','29'])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_relset_1 @ X8 @ X9 @ X10 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['47'])).

thf('49',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('53',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['44','53'])).

thf('55',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('56',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['17','56'])).

thf('58',plain,(
    v1_partfun1 @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['10','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['4','58','59'])).

thf('61',plain,
    ( ( sk_C = sk_D )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','60'])).

thf('62',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['17','56'])).

thf('70',plain,(
    v1_partfun1 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_C = sk_D ),
    inference(demod,[status(thm)],['61','62','70','71'])).

thf('73',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['46','48'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1xLIIhJCaL
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 248 iterations in 0.101s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.21/0.56  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(t142_funct_2, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56           ( ( r1_partfun1 @ C @ D ) =>
% 0.21/0.56             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.56               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.56            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56          ( ![D:$i]:
% 0.21/0.56            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.56                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56              ( ( r1_partfun1 @ C @ D ) =>
% 0.21/0.56                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.56                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.21/0.56  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t148_partfun1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.21/0.56               ( r1_partfun1 @ C @ D ) ) =>
% 0.21/0.56             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.56         (~ (v1_funct_1 @ X18)
% 0.21/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.21/0.56          | ((X21) = (X18))
% 0.21/0.56          | ~ (r1_partfun1 @ X21 @ X18)
% 0.21/0.56          | ~ (v1_partfun1 @ X18 @ X19)
% 0.21/0.56          | ~ (v1_partfun1 @ X21 @ X19)
% 0.21/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.21/0.56          | ~ (v1_funct_1 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.21/0.56          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.56          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.21/0.56          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.21/0.56          | ((X0) = (sk_D))
% 0.21/0.56          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc5_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.56             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.21/0.56          | (v1_partfun1 @ X15 @ X16)
% 0.21/0.56          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.21/0.56          | ~ (v1_funct_1 @ X15)
% 0.21/0.56          | (v1_xboole_0 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (((v1_xboole_0 @ sk_B_1)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1)
% 0.21/0.56        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('10', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.56  thf(t8_boole, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t8_boole])).
% 0.21/0.56  thf('12', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['12'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (((X0) != (k1_xboole_0))
% 0.21/0.56           | ~ (v1_xboole_0 @ sk_B_1)
% 0.21/0.56           | ~ (v1_xboole_0 @ X0)))
% 0.21/0.56         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1)))
% 0.21/0.56         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.56  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.56      inference('simplify_reflect+', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['12'])).
% 0.21/0.56  thf('19', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_D))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf(t9_mcart_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.56                 ( ![C:$i,D:$i]:
% 0.21/0.56                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.56                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X12 : $i]:
% 0.21/0.56         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['12'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_C @ 
% 0.21/0.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf(t5_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.56          | ~ (v1_xboole_0 @ X7)
% 0.21/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.21/0.56           | ~ (r2_hidden @ X0 @ sk_C)))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf(t113_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.56  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['26', '28', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['20', '31'])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X12 : $i]:
% 0.21/0.56         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['12'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_D @ 
% 0.21/0.56         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.56          | ~ (v1_xboole_0 @ X7)
% 0.21/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '42'])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['32', '43'])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('split', [status(esa)], ['12'])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(reflexivity_r2_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.56         ((r2_relset_1 @ X8 @ X9 @ X10 @ X10)
% 0.21/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.21/0.56      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.21/0.56      inference('condensation', [status(thm)], ['47'])).
% 0.21/0.56  thf('49', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C)),
% 0.21/0.56      inference('sup-', [status(thm)], ['46', '48'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (((r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_C))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['45', '49'])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '30'])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '30'])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      (((r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.56      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.56  thf('54', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['44', '53'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.21/0.56      inference('split', [status(esa)], ['12'])).
% 0.21/0.56  thf('56', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.21/0.56  thf('57', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['17', '56'])).
% 0.21/0.56  thf('58', plain, ((v1_partfun1 @ sk_D @ sk_A)),
% 0.21/0.56      inference('clc', [status(thm)], ['10', '57'])).
% 0.21/0.56  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.21/0.56          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.56          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.21/0.56          | ((X0) = (sk_D)))),
% 0.21/0.56      inference('demod', [status(thm)], ['4', '58', '59'])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      ((((sk_C) = (sk_D))
% 0.21/0.56        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.21/0.56        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '60'])).
% 0.21/0.56  thf('62', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.21/0.56          | (v1_partfun1 @ X15 @ X16)
% 0.21/0.56          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.21/0.56          | ~ (v1_funct_1 @ X15)
% 0.21/0.56          | (v1_xboole_0 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (((v1_xboole_0 @ sk_B_1)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.21/0.56        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.56  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('67', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('68', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.21/0.56  thf('69', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['17', '56'])).
% 0.21/0.56  thf('70', plain, ((v1_partfun1 @ sk_C @ sk_A)),
% 0.21/0.56      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.56  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('72', plain, (((sk_C) = (sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['61', '62', '70', '71'])).
% 0.21/0.56  thf('73', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C)),
% 0.21/0.56      inference('sup-', [status(thm)], ['46', '48'])).
% 0.21/0.56  thf('74', plain, ($false),
% 0.21/0.56      inference('demod', [status(thm)], ['0', '72', '73'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
