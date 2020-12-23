%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W01P8Vwjl1

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:09 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 258 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :   21
%              Number of atoms          :  892 (4219 expanded)
%              Number of equality atoms :   70 ( 244 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_2 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X24 = X21 )
      | ~ ( r1_partfun1 @ X24 @ X21 )
      | ~ ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_partfun1 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_2 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

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

thf('25',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C = sk_D )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_E @ X11 @ X12 @ X13 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_E @ X0 @ X1 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_E @ X1 @ X0 @ ( sk_B @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('44',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_E @ X11 @ X12 @ X13 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( r2_hidden @ ( sk_E @ sk_B_2 @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( r2_hidden @ ( sk_E @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_D ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('50',plain,
    ( ( sk_D = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('54',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('55',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_relset_1 @ X7 @ X8 @ X9 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('61',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_E @ X11 @ X12 @ X13 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r2_hidden @ ( sk_E @ sk_B_2 @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_E @ sk_B_2 @ sk_A @ ( sk_B_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('67',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ( sk_C = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( sk_C = k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ sk_D )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_D )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','72'])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','74'])).

thf('76',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ~ ( v1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','76'])).

thf('78',plain,
    ( ( sk_C = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['55'])).

thf('83',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['33','78','83'])).

thf('85',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('86',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','86'])).

thf('88',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['28','87'])).

thf('89',plain,(
    sk_C = sk_D ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['55'])).

thf('92',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','89','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W01P8Vwjl1
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.82/1.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.05  % Solved by: fo/fo7.sh
% 0.82/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.05  % done 780 iterations in 0.594s
% 0.82/1.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.05  % SZS output start Refutation
% 0.82/1.05  thf(sk_C_type, type, sk_C: $i).
% 0.82/1.05  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.82/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.05  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.82/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.82/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.05  thf(sk_D_type, type, sk_D: $i).
% 0.82/1.05  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.82/1.05  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.82/1.05  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.82/1.05  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.82/1.05  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.82/1.05  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.82/1.05  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.82/1.05  thf(sk_B_type, type, sk_B: $i > $i).
% 0.82/1.05  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.82/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.05  thf(t142_funct_2, conjecture,
% 0.82/1.05    (![A:$i,B:$i,C:$i]:
% 0.82/1.05     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.05       ( ![D:$i]:
% 0.82/1.05         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.82/1.05             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.05           ( ( r1_partfun1 @ C @ D ) =>
% 0.82/1.05             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.82/1.05               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.82/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.05    (~( ![A:$i,B:$i,C:$i]:
% 0.82/1.05        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.05            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.05          ( ![D:$i]:
% 0.82/1.05            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.82/1.05                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.05              ( ( r1_partfun1 @ C @ D ) =>
% 0.82/1.05                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.82/1.05                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.82/1.05    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.82/1.05  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D)),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('1', plain,
% 0.82/1.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf('2', plain,
% 0.82/1.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.82/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.05  thf(cc5_funct_2, axiom,
% 0.82/1.05    (![A:$i,B:$i]:
% 0.82/1.05     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.82/1.05       ( ![C:$i]:
% 0.82/1.05         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.05           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.82/1.05             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.82/1.05  thf('3', plain,
% 0.82/1.05      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.82/1.06          | (v1_partfun1 @ X18 @ X19)
% 0.82/1.06          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.82/1.06          | ~ (v1_funct_1 @ X18)
% 0.82/1.06          | (v1_xboole_0 @ X20))),
% 0.82/1.06      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.82/1.06  thf('4', plain,
% 0.82/1.06      (((v1_xboole_0 @ sk_B_2)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_D)
% 0.82/1.06        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_2)
% 0.82/1.06        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['2', '3'])).
% 0.82/1.06  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('7', plain, (((v1_xboole_0 @ sk_B_2) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.82/1.06      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.82/1.06  thf('8', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(t148_partfun1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( ( v1_funct_1 @ C ) & 
% 0.82/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.06       ( ![D:$i]:
% 0.82/1.06         ( ( ( v1_funct_1 @ D ) & 
% 0.82/1.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.06           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.82/1.06               ( r1_partfun1 @ C @ D ) ) =>
% 0.82/1.06             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.82/1.06  thf('9', plain,
% 0.82/1.06      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.82/1.06         (~ (v1_funct_1 @ X21)
% 0.82/1.06          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.82/1.06          | ((X24) = (X21))
% 0.82/1.06          | ~ (r1_partfun1 @ X24 @ X21)
% 0.82/1.06          | ~ (v1_partfun1 @ X21 @ X22)
% 0.82/1.06          | ~ (v1_partfun1 @ X24 @ X22)
% 0.82/1.06          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.82/1.06          | ~ (v1_funct_1 @ X24))),
% 0.82/1.06      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.82/1.06  thf('10', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.82/1.06          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.82/1.06          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.82/1.06          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.82/1.06          | ((X0) = (sk_D))
% 0.82/1.06          | ~ (v1_funct_1 @ sk_D))),
% 0.82/1.06      inference('sup-', [status(thm)], ['8', '9'])).
% 0.82/1.06  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('12', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.82/1.06          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.82/1.06          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.82/1.06          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.82/1.06          | ((X0) = (sk_D)))),
% 0.82/1.06      inference('demod', [status(thm)], ['10', '11'])).
% 0.82/1.06  thf('13', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         ((v1_xboole_0 @ sk_B_2)
% 0.82/1.06          | ((X0) = (sk_D))
% 0.82/1.06          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.82/1.06          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.82/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.82/1.06          | ~ (v1_funct_1 @ X0))),
% 0.82/1.06      inference('sup-', [status(thm)], ['7', '12'])).
% 0.82/1.06  thf('14', plain,
% 0.82/1.06      ((~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.82/1.06        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.82/1.06        | ((sk_C) = (sk_D))
% 0.82/1.06        | (v1_xboole_0 @ sk_B_2))),
% 0.82/1.06      inference('sup-', [status(thm)], ['1', '13'])).
% 0.82/1.06  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('16', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('17', plain,
% 0.82/1.06      ((~ (v1_partfun1 @ sk_C @ sk_A)
% 0.82/1.06        | ((sk_C) = (sk_D))
% 0.82/1.06        | (v1_xboole_0 @ sk_B_2))),
% 0.82/1.06      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.82/1.06  thf('18', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('19', plain,
% 0.82/1.06      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.82/1.06          | (v1_partfun1 @ X18 @ X19)
% 0.82/1.06          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.82/1.06          | ~ (v1_funct_1 @ X18)
% 0.82/1.06          | (v1_xboole_0 @ X20))),
% 0.82/1.06      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.82/1.06  thf('20', plain,
% 0.82/1.06      (((v1_xboole_0 @ sk_B_2)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_2)
% 0.82/1.06        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['18', '19'])).
% 0.82/1.06  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_2)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('23', plain, (((v1_xboole_0 @ sk_B_2) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.82/1.06      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.82/1.06  thf('24', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_C) = (sk_D)))),
% 0.82/1.06      inference('clc', [status(thm)], ['17', '23'])).
% 0.82/1.06  thf(t9_mcart_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.82/1.06          ( ![B:$i]:
% 0.82/1.06            ( ~( ( r2_hidden @ B @ A ) & 
% 0.82/1.06                 ( ![C:$i,D:$i]:
% 0.82/1.06                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.82/1.06                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.82/1.06  thf('25', plain,
% 0.82/1.06      (![X15 : $i]:
% 0.82/1.06         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X15) @ X15))),
% 0.82/1.06      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.82/1.06  thf(d1_xboole_0, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.82/1.06  thf('26', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.82/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.82/1.06  thf('27', plain,
% 0.82/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.82/1.06      inference('sup-', [status(thm)], ['25', '26'])).
% 0.82/1.06  thf('28', plain, ((((sk_C) = (sk_D)) | ((sk_B_2) = (k1_xboole_0)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['24', '27'])).
% 0.82/1.06  thf('29', plain, ((((sk_B_2) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('30', plain,
% 0.82/1.06      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.82/1.06      inference('split', [status(esa)], ['29'])).
% 0.82/1.06  thf('31', plain,
% 0.82/1.06      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('split', [status(esa)], ['29'])).
% 0.82/1.06  thf('32', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('33', plain,
% 0.82/1.06      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_D))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['31', '32'])).
% 0.82/1.06  thf('34', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_C) = (sk_D)))),
% 0.82/1.06      inference('clc', [status(thm)], ['17', '23'])).
% 0.82/1.06  thf('35', plain,
% 0.82/1.06      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.82/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.82/1.06  thf(t4_subset_1, axiom,
% 0.82/1.06    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.82/1.06  thf('36', plain,
% 0.82/1.06      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.82/1.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.82/1.06  thf(t6_relset_1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.06     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.82/1.06       ( ~( ( r2_hidden @ A @ D ) & 
% 0.82/1.06            ( ![E:$i,F:$i]:
% 0.82/1.06              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.82/1.06                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.82/1.06  thf('37', plain,
% 0.82/1.06      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.82/1.06         ((r2_hidden @ (sk_E @ X11 @ X12 @ X13) @ X12)
% 0.82/1.06          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.82/1.06          | ~ (r2_hidden @ X13 @ X14))),
% 0.82/1.06      inference('cnf', [status(esa)], [t6_relset_1])).
% 0.82/1.06  thf('38', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.06         (~ (r2_hidden @ X2 @ k1_xboole_0)
% 0.82/1.06          | (r2_hidden @ (sk_E @ X0 @ X1 @ X2) @ X1))),
% 0.82/1.06      inference('sup-', [status(thm)], ['36', '37'])).
% 0.82/1.06  thf('39', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i]:
% 0.82/1.06         ((v1_xboole_0 @ k1_xboole_0)
% 0.82/1.06          | (r2_hidden @ (sk_E @ X1 @ X0 @ (sk_B @ k1_xboole_0)) @ X0))),
% 0.82/1.06      inference('sup-', [status(thm)], ['35', '38'])).
% 0.82/1.06  thf('40', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.82/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.82/1.06  thf('41', plain,
% 0.82/1.06      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.82/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.82/1.06  thf('42', plain,
% 0.82/1.06      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.82/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.82/1.06  thf('43', plain,
% 0.82/1.06      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('split', [status(esa)], ['29'])).
% 0.82/1.06  thf('44', plain,
% 0.82/1.06      (![X15 : $i]:
% 0.82/1.06         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X15) @ X15))),
% 0.82/1.06      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.82/1.06  thf('45', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('46', plain,
% 0.82/1.06      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.82/1.06         ((r2_hidden @ (sk_E @ X11 @ X12 @ X13) @ X12)
% 0.82/1.06          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.82/1.06          | ~ (r2_hidden @ X13 @ X14))),
% 0.82/1.06      inference('cnf', [status(esa)], [t6_relset_1])).
% 0.82/1.06  thf('47', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (r2_hidden @ X0 @ sk_D)
% 0.82/1.06          | (r2_hidden @ (sk_E @ sk_B_2 @ sk_A @ X0) @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['45', '46'])).
% 0.82/1.06  thf('48', plain,
% 0.82/1.06      ((((sk_D) = (k1_xboole_0))
% 0.82/1.06        | (r2_hidden @ (sk_E @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_D)) @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['44', '47'])).
% 0.82/1.06  thf('49', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.82/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.82/1.06  thf('50', plain, ((((sk_D) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['48', '49'])).
% 0.82/1.06  thf('51', plain,
% 0.82/1.06      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_D) = (k1_xboole_0))))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['43', '50'])).
% 0.82/1.06  thf('52', plain,
% 0.82/1.06      ((![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_D) = (k1_xboole_0))))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['42', '51'])).
% 0.82/1.06  thf('53', plain,
% 0.82/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.82/1.06      inference('sup-', [status(thm)], ['25', '26'])).
% 0.82/1.06  thf('54', plain,
% 0.82/1.06      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.82/1.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.82/1.06  thf(reflexivity_r2_relset_1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.06     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.82/1.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.06       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.82/1.06  thf('55', plain,
% 0.82/1.06      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.82/1.06         ((r2_relset_1 @ X7 @ X8 @ X9 @ X9)
% 0.82/1.06          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.82/1.06          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.82/1.06      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.82/1.06  thf('56', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.06         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.82/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.82/1.06      inference('condensation', [status(thm)], ['55'])).
% 0.82/1.06  thf('57', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.82/1.06      inference('sup-', [status(thm)], ['54', '56'])).
% 0.82/1.06  thf('58', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.06         ((r2_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.82/1.06      inference('sup+', [status(thm)], ['53', '57'])).
% 0.82/1.06  thf('59', plain,
% 0.82/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.82/1.06      inference('sup-', [status(thm)], ['25', '26'])).
% 0.82/1.06  thf('60', plain,
% 0.82/1.06      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('split', [status(esa)], ['29'])).
% 0.82/1.06  thf('61', plain,
% 0.82/1.06      (![X15 : $i]:
% 0.82/1.06         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X15) @ X15))),
% 0.82/1.06      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.82/1.06  thf('62', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('63', plain,
% 0.82/1.06      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.82/1.06         ((r2_hidden @ (sk_E @ X11 @ X12 @ X13) @ X12)
% 0.82/1.06          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.82/1.06          | ~ (r2_hidden @ X13 @ X14))),
% 0.82/1.06      inference('cnf', [status(esa)], [t6_relset_1])).
% 0.82/1.06  thf('64', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (r2_hidden @ X0 @ sk_C)
% 0.82/1.06          | (r2_hidden @ (sk_E @ sk_B_2 @ sk_A @ X0) @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['62', '63'])).
% 0.82/1.06  thf('65', plain,
% 0.82/1.06      ((((sk_C) = (k1_xboole_0))
% 0.82/1.06        | (r2_hidden @ (sk_E @ sk_B_2 @ sk_A @ (sk_B_1 @ sk_C)) @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['61', '64'])).
% 0.82/1.06  thf('66', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.82/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.82/1.06  thf('67', plain, ((((sk_C) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['65', '66'])).
% 0.82/1.06  thf('68', plain,
% 0.82/1.06      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_C) = (k1_xboole_0))))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['60', '67'])).
% 0.82/1.06  thf('69', plain,
% 0.82/1.06      ((![X0 : $i]:
% 0.82/1.06          (~ (v1_xboole_0 @ X0)
% 0.82/1.06           | ~ (v1_xboole_0 @ X0)
% 0.82/1.06           | ((sk_C) = (k1_xboole_0))))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['59', '68'])).
% 0.82/1.06  thf('70', plain,
% 0.82/1.06      ((![X0 : $i]: (((sk_C) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('simplify', [status(thm)], ['69'])).
% 0.82/1.06  thf('71', plain,
% 0.82/1.06      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_D))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['31', '32'])).
% 0.82/1.06  thf('72', plain,
% 0.82/1.06      ((![X0 : $i]:
% 0.82/1.06          (~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ sk_D)
% 0.82/1.06           | ~ (v1_xboole_0 @ X0)))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['70', '71'])).
% 0.82/1.06  thf('73', plain,
% 0.82/1.06      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ X0)))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['58', '72'])).
% 0.82/1.06  thf('74', plain, ((~ (v1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('condensation', [status(thm)], ['73'])).
% 0.82/1.06  thf('75', plain,
% 0.82/1.06      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0)))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['52', '74'])).
% 0.82/1.06  thf('76', plain,
% 0.82/1.06      ((~ (v1_xboole_0 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('condensation', [status(thm)], ['75'])).
% 0.82/1.06  thf('77', plain,
% 0.82/1.06      ((![X0 : $i]: ~ (v1_xboole_0 @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['41', '76'])).
% 0.82/1.06  thf('78', plain, ((((sk_C) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['34', '77'])).
% 0.82/1.06  thf('79', plain,
% 0.82/1.06      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('split', [status(esa)], ['29'])).
% 0.82/1.06  thf('80', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('81', plain,
% 0.82/1.06      (((m1_subset_1 @ sk_C @ 
% 0.82/1.06         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup+', [status(thm)], ['79', '80'])).
% 0.82/1.06  thf('82', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.06         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.82/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.82/1.06      inference('condensation', [status(thm)], ['55'])).
% 0.82/1.06  thf('83', plain,
% 0.82/1.06      (((r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C @ sk_C))
% 0.82/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['81', '82'])).
% 0.82/1.06  thf('84', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.82/1.06      inference('demod', [status(thm)], ['33', '78', '83'])).
% 0.82/1.06  thf('85', plain,
% 0.82/1.06      (~ (((sk_B_2) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.82/1.06      inference('split', [status(esa)], ['29'])).
% 0.82/1.06  thf('86', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.82/1.06      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 0.82/1.06  thf('87', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.82/1.06      inference('simpl_trail', [status(thm)], ['30', '86'])).
% 0.82/1.06  thf('88', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (sk_D)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['28', '87'])).
% 0.82/1.06  thf('89', plain, (((sk_C) = (sk_D))),
% 0.82/1.06      inference('simplify', [status(thm)], ['88'])).
% 0.82/1.06  thf('90', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('91', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.06         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.82/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.82/1.06      inference('condensation', [status(thm)], ['55'])).
% 0.82/1.06  thf('92', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['90', '91'])).
% 0.82/1.06  thf('93', plain, ($false),
% 0.82/1.06      inference('demod', [status(thm)], ['0', '89', '92'])).
% 0.82/1.06  
% 0.82/1.06  % SZS output end Refutation
% 0.82/1.06  
% 0.82/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
