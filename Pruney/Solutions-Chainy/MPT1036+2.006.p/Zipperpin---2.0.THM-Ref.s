%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uwqcoXN8dE

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:14 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 636 expanded)
%              Number of leaves         :   33 ( 199 expanded)
%              Depth                    :   20
%              Number of atoms          : 1069 (10138 expanded)
%              Number of equality atoms :   57 ( 392 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t146_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) )
               => ( ( k1_funct_1 @ B @ D )
                  = ( k1_funct_1 @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ X24 )
        = ( k1_funct_1 @ sk_C_1 @ X24 ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
    | ! [X24: $i] :
        ( ~ ( r2_hidden @ X24 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X24 )
          = ( k1_funct_1 @ sk_C_1 @ X24 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('12',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
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

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,(
    ! [X13: $i] :
      ( zip_tseitin_0 @ X13 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('30',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','30'])).

thf(t132_partfun1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( r1_partfun1 @ A @ B )
            <=> ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( r2_hidden @ ( sk_C @ X21 @ X22 ) @ ( k1_relat_1 @ X22 ) )
      | ( r1_partfun1 @ X22 @ X21 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_partfun1 @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_partfun1 @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42','47'])).

thf('49',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('50',plain,
    ( ! [X24: $i] :
        ( ~ ( r2_hidden @ X24 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X24 )
          = ( k1_funct_1 @ sk_C_1 @ X24 ) ) )
   <= ! [X24: $i] :
        ( ~ ( r2_hidden @ X24 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X24 )
          = ( k1_funct_1 @ sk_C_1 @ X24 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X0 )
          = ( k1_funct_1 @ sk_C_1 @ X0 ) ) )
   <= ! [X24: $i] :
        ( ~ ( r2_hidden @ X24 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X24 )
          = ( k1_funct_1 @ sk_C_1 @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_C_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) ) )
   <= ! [X24: $i] :
        ( ~ ( r2_hidden @ X24 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X24 )
          = ( k1_funct_1 @ sk_C_1 @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k1_funct_1 @ X22 @ ( sk_C @ X21 @ X22 ) )
       != ( k1_funct_1 @ X21 @ ( sk_C @ X21 @ X22 ) ) )
      | ( r1_partfun1 @ X22 @ X21 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('54',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
       != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ! [X24: $i] :
        ( ~ ( r2_hidden @ X24 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X24 )
          = ( k1_funct_1 @ sk_C_1 @ X24 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('58',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('61',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
       != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( r1_partfun1 @ sk_B @ sk_C_1 ) )
   <= ! [X24: $i] :
        ( ~ ( r2_hidden @ X24 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X24 )
          = ( k1_funct_1 @ sk_C_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','59','60'])).

thf('62',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ! [X24: $i] :
        ( ~ ( r2_hidden @ X24 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X24 )
          = ( k1_funct_1 @ sk_C_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ~ ! [X24: $i] :
          ( ~ ( r2_hidden @ X24 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X24 )
            = ( k1_funct_1 @ sk_C_1 @ X24 ) ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,(
    r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['7','65','66'])).

thf('68',plain,(
    r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['5','67'])).

thf('69',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('70',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('71',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( r1_partfun1 @ X22 @ X21 )
      | ( ( k1_funct_1 @ X22 @ X23 )
        = ( k1_funct_1 @ X21 @ X23 ) )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('78',plain,(
    r1_partfun1 @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['7','65'])).

thf('79',plain,(
    r1_partfun1 @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','79','80','81'])).

thf('83',plain,
    ( ( k1_funct_1 @ sk_B @ sk_D )
    = ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','82'])).

thf('84',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['63'])).

thf('85',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['63'])).

thf('86',plain,(
    ( k1_funct_1 @ sk_B @ sk_D )
 != ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['7','65','85'])).

thf('87',plain,(
    ( k1_funct_1 @ sk_B @ sk_D )
 != ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['84','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['83','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uwqcoXN8dE
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:17:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 153 iterations in 0.101s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.55  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.37/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(t146_funct_2, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_funct_1 @ B ) & 
% 0.37/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.37/0.55             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.55           ( ( r1_partfun1 @ B @ C ) <=>
% 0.37/0.55             ( ![D:$i]:
% 0.37/0.55               ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.37/0.55                 ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( ( v1_funct_1 @ B ) & 
% 0.37/0.55            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.55          ( ![C:$i]:
% 0.37/0.55            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.37/0.55                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.37/0.55              ( ( r1_partfun1 @ B @ C ) <=>
% 0.37/0.55                ( ![D:$i]:
% 0.37/0.55                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.37/0.55                    ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t146_funct_2])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55        | ~ (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))
% 0.37/0.55         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.37/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.55  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (((r2_hidden @ sk_D @ (k1_relat_1 @ sk_B)))
% 0.37/0.55         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.37/0.55      inference('demod', [status(thm)], ['1', '4'])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X24 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X24 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55          | ((k1_funct_1 @ sk_B @ X24) = (k1_funct_1 @ sk_C_1 @ X24))
% 0.37/0.55          | (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (((r1_partfun1 @ sk_B @ sk_C_1)) | 
% 0.37/0.55       (![X24 : $i]:
% 0.37/0.55          (~ (r2_hidden @ X24 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55           | ((k1_funct_1 @ sk_B @ X24) = (k1_funct_1 @ sk_C_1 @ X24))))),
% 0.37/0.55      inference('split', [status(esa)], ['6'])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(dt_k1_relset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.55         ((m1_subset_1 @ (k1_relset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 0.37/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      ((m1_subset_1 @ (k1_relat_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.37/0.55  thf(t3_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf('15', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d1_funct_2, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_1, axiom,
% 0.37/0.55    (![C:$i,B:$i,A:$i]:
% 0.37/0.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.55         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.37/0.55          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 0.37/0.55          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 0.37/0.55        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_C_1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.37/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 0.37/0.55        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.37/0.55      inference('demod', [status(thm)], ['17', '20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.55  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.55  thf(zf_stmt_4, axiom,
% 0.37/0.55    (![B:$i,A:$i]:
% 0.37/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.55       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.55  thf(zf_stmt_5, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.55         (~ (zip_tseitin_0 @ X18 @ X19)
% 0.37/0.55          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 0.37/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (((zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 0.37/0.55        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i]:
% 0.37/0.55         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i]:
% 0.37/0.55         ((zip_tseitin_0 @ X13 @ X14) | ((X14) != (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.37/0.55  thf('27', plain, (![X13 : $i]: (zip_tseitin_0 @ X13 @ k1_xboole_0)),
% 0.37/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.37/0.55      inference('sup+', [status(thm)], ['25', '27'])).
% 0.37/0.55  thf('29', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.37/0.55      inference('eq_fact', [status(thm)], ['28'])).
% 0.37/0.55  thf('30', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)),
% 0.37/0.55      inference('demod', [status(thm)], ['24', '29'])).
% 0.37/0.55  thf('31', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['21', '30'])).
% 0.37/0.55  thf(t132_partfun1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.55           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.55             ( ( r1_partfun1 @ A @ B ) <=>
% 0.37/0.55               ( ![C:$i]:
% 0.37/0.55                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.37/0.55                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X21)
% 0.37/0.55          | ~ (v1_funct_1 @ X21)
% 0.37/0.55          | (r2_hidden @ (sk_C @ X21 @ X22) @ (k1_relat_1 @ X22))
% 0.37/0.55          | (r1_partfun1 @ X22 @ X21)
% 0.37/0.55          | ~ (r1_tarski @ (k1_relat_1 @ X22) @ (k1_relat_1 @ X21))
% 0.37/0.55          | ~ (v1_funct_1 @ X22)
% 0.37/0.55          | ~ (v1_relat_1 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | (r1_partfun1 @ X0 @ sk_C_1)
% 0.37/0.55          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.55          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.55          | ~ (v1_relat_1 @ sk_C_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.55  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(cc2_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.37/0.55          | (v1_relat_1 @ X3)
% 0.37/0.55          | ~ (v1_relat_1 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.55  thf(fc6_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.55  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | (r1_partfun1 @ X0 @ sk_C_1)
% 0.37/0.55          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['33', '34', '39'])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.37/0.55        | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_B)
% 0.37/0.55        | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['14', '40'])).
% 0.37/0.55  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.37/0.55          | (v1_relat_1 @ X3)
% 0.37/0.55          | ~ (v1_relat_1 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.55  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.37/0.55        | (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['41', '42', '47'])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      ((![X24 : $i]:
% 0.37/0.55          (~ (r2_hidden @ X24 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55           | ((k1_funct_1 @ sk_B @ X24) = (k1_funct_1 @ sk_C_1 @ X24))))
% 0.37/0.55         <= ((![X24 : $i]:
% 0.37/0.55                (~ (r2_hidden @ X24 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55                 | ((k1_funct_1 @ sk_B @ X24) = (k1_funct_1 @ sk_C_1 @ X24)))))),
% 0.37/0.55      inference('split', [status(esa)], ['6'])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.37/0.55           | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))))
% 0.37/0.55         <= ((![X24 : $i]:
% 0.37/0.55                (~ (r2_hidden @ X24 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55                 | ((k1_funct_1 @ sk_B @ X24) = (k1_funct_1 @ sk_C_1 @ X24)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      ((((r1_partfun1 @ sk_B @ sk_C_1)
% 0.37/0.55         | ((k1_funct_1 @ sk_B @ (sk_C @ sk_C_1 @ sk_B))
% 0.37/0.55             = (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))))
% 0.37/0.55         <= ((![X24 : $i]:
% 0.37/0.55                (~ (r2_hidden @ X24 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55                 | ((k1_funct_1 @ sk_B @ X24) = (k1_funct_1 @ sk_C_1 @ X24)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['48', '51'])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X21)
% 0.37/0.55          | ~ (v1_funct_1 @ X21)
% 0.37/0.55          | ((k1_funct_1 @ X22 @ (sk_C @ X21 @ X22))
% 0.37/0.55              != (k1_funct_1 @ X21 @ (sk_C @ X21 @ X22)))
% 0.37/0.55          | (r1_partfun1 @ X22 @ X21)
% 0.37/0.55          | ~ (r1_tarski @ (k1_relat_1 @ X22) @ (k1_relat_1 @ X21))
% 0.37/0.55          | ~ (v1_funct_1 @ X22)
% 0.37/0.55          | ~ (v1_relat_1 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.37/0.55  thf('54', plain,
% 0.37/0.55      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.37/0.55           != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))
% 0.37/0.55         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.37/0.55         | ~ (v1_relat_1 @ sk_B)
% 0.37/0.55         | ~ (v1_funct_1 @ sk_B)
% 0.37/0.55         | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C_1))
% 0.37/0.55         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.37/0.55         | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.55         | ~ (v1_relat_1 @ sk_C_1)))
% 0.37/0.55         <= ((![X24 : $i]:
% 0.37/0.55                (~ (r2_hidden @ X24 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55                 | ((k1_funct_1 @ sk_B @ X24) = (k1_funct_1 @ sk_C_1 @ X24)))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.55  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.55  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('57', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['21', '30'])).
% 0.37/0.55  thf('58', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf('59', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.37/0.55           != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))
% 0.37/0.55         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.37/0.55         | (r1_partfun1 @ sk_B @ sk_C_1)))
% 0.37/0.55         <= ((![X24 : $i]:
% 0.37/0.55                (~ (r2_hidden @ X24 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55                 | ((k1_funct_1 @ sk_B @ X24) = (k1_funct_1 @ sk_C_1 @ X24)))))),
% 0.37/0.55      inference('demod', [status(thm)],
% 0.37/0.55                ['54', '55', '56', '57', '58', '59', '60'])).
% 0.37/0.55  thf('62', plain,
% 0.37/0.55      (((r1_partfun1 @ sk_B @ sk_C_1))
% 0.37/0.55         <= ((![X24 : $i]:
% 0.37/0.55                (~ (r2_hidden @ X24 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55                 | ((k1_funct_1 @ sk_B @ X24) = (k1_funct_1 @ sk_C_1 @ X24)))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['61'])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D))
% 0.37/0.55        | ~ (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      ((~ (r1_partfun1 @ sk_B @ sk_C_1)) <= (~ ((r1_partfun1 @ sk_B @ sk_C_1)))),
% 0.37/0.55      inference('split', [status(esa)], ['63'])).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      (~
% 0.37/0.55       (![X24 : $i]:
% 0.37/0.55          (~ (r2_hidden @ X24 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.37/0.55           | ((k1_funct_1 @ sk_B @ X24) = (k1_funct_1 @ sk_C_1 @ X24)))) | 
% 0.37/0.55       ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['62', '64'])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))) | 
% 0.37/0.55       ~ ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('67', plain, (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['7', '65', '66'])).
% 0.37/0.55  thf('68', plain, ((r2_hidden @ sk_D @ (k1_relat_1 @ sk_B))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['5', '67'])).
% 0.37/0.55  thf('69', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf('70', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['21', '30'])).
% 0.37/0.55  thf('71', plain,
% 0.37/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X21)
% 0.37/0.55          | ~ (v1_funct_1 @ X21)
% 0.37/0.55          | ~ (r1_partfun1 @ X22 @ X21)
% 0.37/0.55          | ((k1_funct_1 @ X22 @ X23) = (k1_funct_1 @ X21 @ X23))
% 0.37/0.55          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X22))
% 0.37/0.55          | ~ (r1_tarski @ (k1_relat_1 @ X22) @ (k1_relat_1 @ X21))
% 0.37/0.55          | ~ (v1_funct_1 @ X22)
% 0.37/0.55          | ~ (v1_relat_1 @ X22))),
% 0.37/0.55      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.37/0.55  thf('72', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.37/0.55          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_C_1 @ X1))
% 0.37/0.55          | ~ (r1_partfun1 @ X0 @ sk_C_1)
% 0.37/0.55          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.55          | ~ (v1_relat_1 @ sk_C_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['70', '71'])).
% 0.37/0.55  thf('73', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('74', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.55  thf('75', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_funct_1 @ X0)
% 0.37/0.55          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.37/0.55          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_C_1 @ X1))
% 0.37/0.55          | ~ (r1_partfun1 @ X0 @ sk_C_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.37/0.55  thf('76', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_partfun1 @ sk_B @ sk_C_1)
% 0.37/0.55          | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))
% 0.37/0.55          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.37/0.55          | ~ (v1_funct_1 @ sk_B)
% 0.37/0.55          | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['69', '75'])).
% 0.37/0.55  thf('77', plain,
% 0.37/0.55      (((r1_partfun1 @ sk_B @ sk_C_1)) <= (((r1_partfun1 @ sk_B @ sk_C_1)))),
% 0.37/0.55      inference('split', [status(esa)], ['6'])).
% 0.37/0.55  thf('78', plain, (((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['7', '65'])).
% 0.37/0.55  thf('79', plain, ((r1_partfun1 @ sk_B @ sk_C_1)),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['77', '78'])).
% 0.37/0.55  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('81', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.55  thf('82', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))
% 0.37/0.55          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['76', '79', '80', '81'])).
% 0.37/0.55  thf('83', plain,
% 0.37/0.55      (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['68', '82'])).
% 0.37/0.55  thf('84', plain,
% 0.37/0.55      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D)))
% 0.37/0.55         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))))),
% 0.37/0.55      inference('split', [status(esa)], ['63'])).
% 0.37/0.55  thf('85', plain,
% 0.37/0.55      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))) | 
% 0.37/0.55       ~ ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.37/0.55      inference('split', [status(esa)], ['63'])).
% 0.37/0.55  thf('86', plain,
% 0.37/0.55      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['7', '65', '85'])).
% 0.37/0.55  thf('87', plain,
% 0.37/0.55      (((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['84', '86'])).
% 0.37/0.55  thf('88', plain, ($false),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['83', '87'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
