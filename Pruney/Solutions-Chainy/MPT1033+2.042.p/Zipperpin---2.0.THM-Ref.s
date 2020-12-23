%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eqkyVbsAnR

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:10 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 235 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  703 (3392 expanded)
%              Number of equality atoms :   58 ( 250 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X25 = X22 )
      | ~ ( r1_partfun1 @ X25 @ X22 )
      | ~ ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_partfun1 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_2 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_2 ) )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('21',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','28'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','34'])).

thf('36',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','46'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('48',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['47','51'])).

thf('53',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('54',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['19','54'])).

thf('56',plain,(
    v1_partfun1 @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['10','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['4','56','57'])).

thf('59',plain,
    ( ( sk_C = sk_D )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','58'])).

thf('60',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['19','54'])).

thf('68',plain,(
    v1_partfun1 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_C = sk_D ),
    inference(demod,[status(thm)],['59','60','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['49'])).

thf('73',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eqkyVbsAnR
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 249 iterations in 0.156s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.42/0.60  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.42/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.60  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.42/0.60  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.42/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(t142_funct_2, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60       ( ![D:$i]:
% 0.42/0.60         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60           ( ( r1_partfun1 @ C @ D ) =>
% 0.42/0.60             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.42/0.60               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60          ( ![D:$i]:
% 0.42/0.60            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.60                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60              ( ( r1_partfun1 @ C @ D ) =>
% 0.42/0.60                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.42/0.60                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.42/0.60  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t148_partfun1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60       ( ![D:$i]:
% 0.42/0.60         ( ( ( v1_funct_1 @ D ) & 
% 0.42/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.42/0.60               ( r1_partfun1 @ C @ D ) ) =>
% 0.42/0.60             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.42/0.60         (~ (v1_funct_1 @ X22)
% 0.42/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.42/0.60          | ((X25) = (X22))
% 0.42/0.60          | ~ (r1_partfun1 @ X25 @ X22)
% 0.42/0.60          | ~ (v1_partfun1 @ X22 @ X23)
% 0.42/0.60          | ~ (v1_partfun1 @ X25 @ X23)
% 0.42/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.42/0.60          | ~ (v1_funct_1 @ X25))),
% 0.42/0.60      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.42/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.42/0.60          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.42/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.42/0.60          | ((X0) = (sk_D))
% 0.42/0.60          | ~ (v1_funct_1 @ sk_D))),
% 0.42/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(cc5_funct_2, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.60       ( ![C:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.42/0.60             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.42/0.60          | (v1_partfun1 @ X19 @ X20)
% 0.42/0.60          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.42/0.60          | ~ (v1_funct_1 @ X19)
% 0.42/0.60          | (v1_xboole_0 @ X21))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (((v1_xboole_0 @ sk_B_2)
% 0.42/0.60        | ~ (v1_funct_1 @ sk_D)
% 0.42/0.60        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_2)
% 0.42/0.60        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.60  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('10', plain, (((v1_xboole_0 @ sk_B_2) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.42/0.60  thf(l13_xboole_0, axiom,
% 0.42/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.60      inference('sup+', [status(thm)], ['11', '12'])).
% 0.42/0.60  thf('14', plain, ((((sk_B_2) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['14'])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      ((![X0 : $i]:
% 0.42/0.60          (((X0) != (k1_xboole_0))
% 0.42/0.60           | ~ (v1_xboole_0 @ X0)
% 0.42/0.60           | ~ (v1_xboole_0 @ sk_B_2)))
% 0.42/0.60         <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['13', '15'])).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (((~ (v1_xboole_0 @ sk_B_2) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.42/0.60         <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.42/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.42/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.42/0.60  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      ((~ (v1_xboole_0 @ sk_B_2)) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.42/0.60      inference('simplify_reflect+', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['14'])).
% 0.42/0.60  thf('21', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_D))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.60  thf(t9_mcart_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.60          ( ![B:$i]:
% 0.42/0.60            ( ~( ( r2_hidden @ B @ A ) & 
% 0.42/0.60                 ( ![C:$i,D:$i]:
% 0.42/0.60                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.42/0.60                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (![X16 : $i]:
% 0.42/0.60         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X16) @ X16))),
% 0.42/0.60      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['14'])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_C @ 
% 0.42/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['24', '25'])).
% 0.42/0.60  thf(t113_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i]:
% 0.42/0.60         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['27'])).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['26', '28'])).
% 0.42/0.60  thf(t5_subset, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.42/0.60          ( v1_xboole_0 @ C ) ) ))).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X9 @ X10)
% 0.42/0.60          | ~ (v1_xboole_0 @ X11)
% 0.42/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t5_subset])).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C)))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.60  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['23', '33'])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ sk_D))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['22', '34'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (![X16 : $i]:
% 0.42/0.60         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X16) @ X16))),
% 0.42/0.60      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['14'])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('39', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_D @ 
% 0.42/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['37', '38'])).
% 0.42/0.60  thf('40', plain,
% 0.42/0.60      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['27'])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X9 @ X10)
% 0.42/0.60          | ~ (v1_xboole_0 @ X11)
% 0.42/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t5_subset])).
% 0.42/0.60  thf('43', plain,
% 0.42/0.60      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.60  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.60  thf('45', plain,
% 0.42/0.60      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['36', '45'])).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ k1_xboole_0))
% 0.42/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['35', '46'])).
% 0.42/0.60  thf(t4_subset_1, axiom,
% 0.42/0.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.60  thf('48', plain,
% 0.42/0.60      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.42/0.60  thf(reflexivity_r2_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.42/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.60       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.42/0.60  thf('49', plain,
% 0.42/0.60      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.60         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 0.42/0.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.42/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.42/0.60      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.42/0.60  thf('50', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.42/0.60      inference('condensation', [status(thm)], ['49'])).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.42/0.60      inference('sup-', [status(thm)], ['48', '50'])).
% 0.42/0.60  thf('52', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['47', '51'])).
% 0.42/0.60  thf('53', plain,
% 0.42/0.60      (~ (((sk_B_2) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.42/0.60      inference('split', [status(esa)], ['14'])).
% 0.42/0.60  thf('54', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.42/0.60      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.42/0.60  thf('55', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['19', '54'])).
% 0.42/0.60  thf('56', plain, ((v1_partfun1 @ sk_D @ sk_A)),
% 0.42/0.60      inference('clc', [status(thm)], ['10', '55'])).
% 0.42/0.60  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('58', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_funct_1 @ X0)
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.42/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.42/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.42/0.60          | ((X0) = (sk_D)))),
% 0.42/0.60      inference('demod', [status(thm)], ['4', '56', '57'])).
% 0.42/0.60  thf('59', plain,
% 0.42/0.60      ((((sk_C) = (sk_D))
% 0.42/0.60        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.42/0.60        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.42/0.60        | ~ (v1_funct_1 @ sk_C))),
% 0.42/0.60      inference('sup-', [status(thm)], ['1', '58'])).
% 0.42/0.60  thf('60', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('61', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('62', plain,
% 0.42/0.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.42/0.60          | (v1_partfun1 @ X19 @ X20)
% 0.42/0.60          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.42/0.60          | ~ (v1_funct_1 @ X19)
% 0.42/0.60          | (v1_xboole_0 @ X21))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.42/0.60  thf('63', plain,
% 0.42/0.60      (((v1_xboole_0 @ sk_B_2)
% 0.42/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.60        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 0.42/0.60        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['61', '62'])).
% 0.42/0.60  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('65', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('66', plain, (((v1_xboole_0 @ sk_B_2) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.42/0.60  thf('67', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['19', '54'])).
% 0.42/0.60  thf('68', plain, ((v1_partfun1 @ sk_C @ sk_A)),
% 0.42/0.60      inference('clc', [status(thm)], ['66', '67'])).
% 0.42/0.60  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('70', plain, (((sk_C) = (sk_D))),
% 0.42/0.60      inference('demod', [status(thm)], ['59', '60', '68', '69'])).
% 0.42/0.60  thf('71', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('72', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.42/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.42/0.60      inference('condensation', [status(thm)], ['49'])).
% 0.42/0.60  thf('73', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_C)),
% 0.42/0.60      inference('sup-', [status(thm)], ['71', '72'])).
% 0.42/0.60  thf('74', plain, ($false),
% 0.42/0.60      inference('demod', [status(thm)], ['0', '70', '73'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
