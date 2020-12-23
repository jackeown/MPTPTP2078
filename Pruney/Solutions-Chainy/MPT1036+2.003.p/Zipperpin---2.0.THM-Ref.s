%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d4WU2n9hYX

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 594 expanded)
%              Number of leaves         :   32 ( 185 expanded)
%              Depth                    :   20
%              Number of atoms          : 1045 (9942 expanded)
%              Number of equality atoms :   57 ( 392 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X23: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ X23 )
        = ( k1_funct_1 @ sk_C_1 @ X23 ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
    | ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X23 )
          = ( k1_funct_1 @ sk_C_1 @ X23 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,(
    ! [X12: $i] :
      ( zip_tseitin_0 @ X12 @ k1_xboole_0 ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( r2_hidden @ ( sk_C @ X20 @ X21 ) @ ( k1_relat_1 @ X21 ) )
      | ( r1_partfun1 @ X21 @ X20 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_partfun1 @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['39','40','43'])).

thf('45',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,
    ( ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X23 )
          = ( k1_funct_1 @ sk_C_1 @ X23 ) ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X23 )
          = ( k1_funct_1 @ sk_C_1 @ X23 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X0 )
          = ( k1_funct_1 @ sk_C_1 @ X0 ) ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X23 )
          = ( k1_funct_1 @ sk_C_1 @ X23 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_C_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X23 )
          = ( k1_funct_1 @ sk_C_1 @ X23 ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k1_funct_1 @ X21 @ ( sk_C @ X20 @ X21 ) )
       != ( k1_funct_1 @ X20 @ ( sk_C @ X20 @ X21 ) ) )
      | ( r1_partfun1 @ X21 @ X20 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('50',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
       != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X23 )
          = ( k1_funct_1 @ sk_C_1 @ X23 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('52',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('54',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('55',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('57',plain,
    ( ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) )
       != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_C_1 @ sk_B ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( r1_partfun1 @ sk_B @ sk_C_1 ) )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X23 )
          = ( k1_funct_1 @ sk_C_1 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54','55','56'])).

thf('58',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ! [X23: $i] :
        ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X23 )
          = ( k1_funct_1 @ sk_C_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ~ ! [X23: $i] :
          ( ~ ( r2_hidden @ X23 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X23 )
            = ( k1_funct_1 @ sk_C_1 @ X23 ) ) )
    | ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,(
    r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['7','61','62'])).

thf('64',plain,(
    r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['5','63'])).

thf('65',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('66',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('67',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r1_partfun1 @ X21 @ X20 )
      | ( ( k1_funct_1 @ X21 @ X22 )
        = ( k1_funct_1 @ X20 @ X22 ) )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('68',plain,(
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
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_C_1 @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_B @ sk_C_1 )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_1 )
   <= ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('74',plain,(
    r1_partfun1 @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['7','61'])).

thf('75',plain,(
    r1_partfun1 @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','75','76','77'])).

thf('79',plain,
    ( ( k1_funct_1 @ sk_B @ sk_D )
    = ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['64','78'])).

thf('80',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['59'])).

thf('81',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_1 @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['59'])).

thf('82',plain,(
    ( k1_funct_1 @ sk_B @ sk_D )
 != ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['7','61','81'])).

thf('83',plain,(
    ( k1_funct_1 @ sk_B @ sk_D )
 != ( k1_funct_1 @ sk_C_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d4WU2n9hYX
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:29:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 137 iterations in 0.119s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(t146_funct_2, conjecture,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ B ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.54             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54           ( ( r1_partfun1 @ B @ C ) <=>
% 0.21/0.54             ( ![D:$i]:
% 0.21/0.54               ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.21/0.54                 ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i]:
% 0.21/0.54        ( ( ( v1_funct_1 @ B ) & 
% 0.21/0.54            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54          ( ![C:$i]:
% 0.21/0.54            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.54                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.54              ( ( r1_partfun1 @ B @ C ) <=>
% 0.21/0.54                ( ![D:$i]:
% 0.21/0.54                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.21/0.54                    ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t146_funct_2])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54        | ~ (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))
% 0.21/0.54         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.54  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (((r2_hidden @ sk_D @ (k1_relat_1 @ sk_B)))
% 0.21/0.54         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.54      inference('demod', [status(thm)], ['1', '4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X23 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54          | ((k1_funct_1 @ sk_B @ X23) = (k1_funct_1 @ sk_C_1 @ X23))
% 0.21/0.54          | (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (((r1_partfun1 @ sk_B @ sk_C_1)) | 
% 0.21/0.54       (![X23 : $i]:
% 0.21/0.54          (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54           | ((k1_funct_1 @ sk_B @ X23) = (k1_funct_1 @ sk_C_1 @ X23))))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k1_relset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.21/0.54          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      ((m1_subset_1 @ (k1_relat_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d1_funct_2, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_1, axiom,
% 0.21/0.54    (![C:$i,B:$i,A:$i]:
% 0.21/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.21/0.54          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.21/0.54          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 0.21/0.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_C_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.21/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 0.21/0.54        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['17', '20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.54  thf(zf_stmt_4, axiom,
% 0.21/0.54    (![B:$i,A:$i]:
% 0.21/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.54  thf(zf_stmt_5, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.54         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.21/0.54          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.21/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (((zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)
% 0.21/0.54        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X12 @ X13) | ((X13) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.54  thf('27', plain, (![X12 : $i]: (zip_tseitin_0 @ X12 @ k1_xboole_0)),
% 0.21/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.21/0.54      inference('sup+', [status(thm)], ['25', '27'])).
% 0.21/0.54  thf('29', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.21/0.54      inference('eq_fact', [status(thm)], ['28'])).
% 0.21/0.54  thf('30', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_A @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['24', '29'])).
% 0.21/0.54  thf('31', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['21', '30'])).
% 0.21/0.54  thf(t132_partfun1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.54             ( ( r1_partfun1 @ A @ B ) <=>
% 0.21/0.54               ( ![C:$i]:
% 0.21/0.54                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.54                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X20)
% 0.21/0.54          | ~ (v1_funct_1 @ X20)
% 0.21/0.54          | (r2_hidden @ (sk_C @ X20 @ X21) @ (k1_relat_1 @ X21))
% 0.21/0.54          | (r1_partfun1 @ X21 @ X20)
% 0.21/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 0.21/0.54          | ~ (v1_funct_1 @ X21)
% 0.21/0.54          | ~ (v1_relat_1 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | (r1_partfun1 @ X0 @ sk_C_1)
% 0.21/0.54          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ (k1_relat_1 @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.54          | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( v1_relat_1 @ C ) ))).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.54         ((v1_relat_1 @ X3)
% 0.21/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.54  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | (r1_partfun1 @ X0 @ sk_C_1)
% 0.21/0.54          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34', '37'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.21/0.54        | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.21/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '38'])).
% 0.21/0.54  thf('40', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.54         ((v1_relat_1 @ X3)
% 0.21/0.54          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.54  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.21/0.54        | (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['39', '40', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      ((![X23 : $i]:
% 0.21/0.54          (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54           | ((k1_funct_1 @ sk_B @ X23) = (k1_funct_1 @ sk_C_1 @ X23))))
% 0.21/0.54         <= ((![X23 : $i]:
% 0.21/0.54                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B @ X23) = (k1_funct_1 @ sk_C_1 @ X23)))))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.21/0.54           | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))))
% 0.21/0.54         <= ((![X23 : $i]:
% 0.21/0.54                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B @ X23) = (k1_funct_1 @ sk_C_1 @ X23)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      ((((r1_partfun1 @ sk_B @ sk_C_1)
% 0.21/0.54         | ((k1_funct_1 @ sk_B @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.54             = (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))))
% 0.21/0.54         <= ((![X23 : $i]:
% 0.21/0.54                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B @ X23) = (k1_funct_1 @ sk_C_1 @ X23)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X20)
% 0.21/0.54          | ~ (v1_funct_1 @ X20)
% 0.21/0.54          | ((k1_funct_1 @ X21 @ (sk_C @ X20 @ X21))
% 0.21/0.54              != (k1_funct_1 @ X20 @ (sk_C @ X20 @ X21)))
% 0.21/0.54          | (r1_partfun1 @ X21 @ X20)
% 0.21/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 0.21/0.54          | ~ (v1_funct_1 @ X21)
% 0.21/0.54          | ~ (v1_relat_1 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.54           != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))
% 0.21/0.54         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.21/0.54         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.54         | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54         | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C_1))
% 0.21/0.54         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.21/0.54         | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.54         | ~ (v1_relat_1 @ sk_C_1)))
% 0.21/0.54         <= ((![X23 : $i]:
% 0.21/0.54                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B @ X23) = (k1_funct_1 @ sk_C_1 @ X23)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.54  thf('52', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('53', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['21', '30'])).
% 0.21/0.54  thf('54', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('55', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B))
% 0.21/0.54           != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_C_1 @ sk_B)))
% 0.21/0.54         | (r1_partfun1 @ sk_B @ sk_C_1)
% 0.21/0.54         | (r1_partfun1 @ sk_B @ sk_C_1)))
% 0.21/0.54         <= ((![X23 : $i]:
% 0.21/0.54                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B @ X23) = (k1_funct_1 @ sk_C_1 @ X23)))))),
% 0.21/0.54      inference('demod', [status(thm)],
% 0.21/0.54                ['50', '51', '52', '53', '54', '55', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (((r1_partfun1 @ sk_B @ sk_C_1))
% 0.21/0.54         <= ((![X23 : $i]:
% 0.21/0.54                (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54                 | ((k1_funct_1 @ sk_B @ X23) = (k1_funct_1 @ sk_C_1 @ X23)))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D))
% 0.21/0.54        | ~ (r1_partfun1 @ sk_B @ sk_C_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      ((~ (r1_partfun1 @ sk_B @ sk_C_1)) <= (~ ((r1_partfun1 @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['59'])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      (~
% 0.21/0.54       (![X23 : $i]:
% 0.21/0.54          (~ (r2_hidden @ X23 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.54           | ((k1_funct_1 @ sk_B @ X23) = (k1_funct_1 @ sk_C_1 @ X23)))) | 
% 0.21/0.54       ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['58', '60'])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))) | 
% 0.21/0.54       ~ ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('63', plain, (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['7', '61', '62'])).
% 0.21/0.54  thf('64', plain, ((r2_hidden @ sk_D @ (k1_relat_1 @ sk_B))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['5', '63'])).
% 0.21/0.54  thf('65', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('66', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['21', '30'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X20)
% 0.21/0.54          | ~ (v1_funct_1 @ X20)
% 0.21/0.54          | ~ (r1_partfun1 @ X21 @ X20)
% 0.21/0.54          | ((k1_funct_1 @ X21 @ X22) = (k1_funct_1 @ X20 @ X22))
% 0.21/0.54          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 0.21/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20))
% 0.21/0.54          | ~ (v1_funct_1 @ X21)
% 0.21/0.54          | ~ (v1_relat_1 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.54          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_C_1 @ X1))
% 0.21/0.54          | ~ (r1_partfun1 @ X0 @ sk_C_1)
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.54          | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.54  thf('69', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('70', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.54          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_C_1 @ X1))
% 0.21/0.54          | ~ (r1_partfun1 @ X0 @ sk_C_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_partfun1 @ sk_B @ sk_C_1)
% 0.21/0.54          | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.21/0.54          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.54          | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['65', '71'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      (((r1_partfun1 @ sk_B @ sk_C_1)) <= (((r1_partfun1 @ sk_B @ sk_C_1)))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('74', plain, (((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['7', '61'])).
% 0.21/0.54  thf('75', plain, ((r1_partfun1 @ sk_B @ sk_C_1)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['73', '74'])).
% 0.21/0.54  thf('76', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_1 @ X0))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['72', '75', '76', '77'])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))),
% 0.21/0.54      inference('sup-', [status(thm)], ['64', '78'])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D)))
% 0.21/0.54         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.54      inference('split', [status(esa)], ['59'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D))) | 
% 0.21/0.54       ~ ((r1_partfun1 @ sk_B @ sk_C_1))),
% 0.21/0.54      inference('split', [status(esa)], ['59'])).
% 0.21/0.54  thf('82', plain,
% 0.21/0.54      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['7', '61', '81'])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      (((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_1 @ sk_D))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.21/0.54  thf('84', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['79', '83'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
