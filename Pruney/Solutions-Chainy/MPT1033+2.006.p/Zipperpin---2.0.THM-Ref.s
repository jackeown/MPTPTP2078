%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bq2a3JFWyX

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:04 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 832 expanded)
%              Number of leaves         :   44 ( 261 expanded)
%              Depth                    :   23
%              Number of atoms          : 1577 (13598 expanded)
%              Number of equality atoms :  117 ( 693 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('0',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_D_2 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( v1_partfun1 @ X41 @ X42 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X41 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_D_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D_2 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('12',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( X47 = X44 )
      | ~ ( r1_partfun1 @ X47 @ X44 )
      | ~ ( v1_partfun1 @ X44 @ X45 )
      | ~ ( v1_partfun1 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D_2 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D_2 )
      | ( X0 = sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D_2 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D_2 )
      | ( X0 = sk_D_2 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( X0 = sk_D_2 )
      | ~ ( r1_partfun1 @ X0 @ sk_D_2 )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_partfun1 @ sk_C_2 @ sk_A )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D_2 )
    | ( sk_C_2 = sk_D_2 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_partfun1 @ sk_C_2 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_partfun1 @ sk_C_2 @ sk_A )
    | ( sk_C_2 = sk_D_2 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( v1_partfun1 @ X41 @ X42 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X41 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_2 = sk_D_2 ) ),
    inference(clc,[status(thm)],['20','26'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C_2 = sk_D_2 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C_2 = sk_D_2 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('36',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r2_relset_1 @ X37 @ X38 @ X39 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','38'])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['3','41'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('43',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( sk_B @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X19: $i,X21: $i,X23: $i,X24: $i] :
      ( ( X21
       != ( k2_relat_1 @ X19 ) )
      | ( r2_hidden @ X23 @ X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X19 ) )
      | ( X23
       != ( k1_funct_1 @ X19 @ X24 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('47',plain,(
    ! [X19: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X19 @ X24 ) @ ( k2_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_2 = sk_D_2 ) ),
    inference(clc,[status(thm)],['20','26'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('56',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('57',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['54','57'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = sk_D_2 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['49','62'])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2 = sk_D_2 ) ),
    inference('sup-',[status(thm)],['48','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2 = sk_D_2 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('69',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('71',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('72',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('73',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( X28 = X27 )
      | ( r2_hidden @ ( sk_C_1 @ X27 @ X28 ) @ ( k1_relat_1 @ X28 ) )
      | ( ( k1_relat_1 @ X28 )
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('75',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('76',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('77',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X1 ) )
        = X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ ( k6_relat_1 @ k1_xboole_0 ) ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2 = sk_D_2 )
    | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) )
      = sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['71','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('83',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ ( k6_relat_1 @ k1_xboole_0 ) ) @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_C_2 = sk_D_2 )
    | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('84',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('85',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) )
      = sk_C_2 )
    | ( sk_C_2 = sk_D_2 )
    | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ ( sk_C_1 @ sk_C_2 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C_1 @ sk_C_2 @ ( k6_relat_1 @ k1_xboole_0 ) ) )
    | ( sk_C_2 = sk_D_2 )
    | ( sk_C_2 = sk_D_2 )
    | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['70','85'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('87',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('88',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( sk_C_2 = sk_D_2 )
    | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C_2 ) )
      = sk_C_2 )
    | ( sk_C_2 = sk_D_2 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_C_2 )
    | ( sk_C_2 = sk_D_2 )
    | ( sk_C_2 = sk_D_2 ) ),
    inference('sup+',[status(thm)],['69','91'])).

thf('93',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_C_2 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('95',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_2 = sk_D_2 ) ),
    inference(clc,[status(thm)],['20','26'])).

thf('96',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v5_relat_1 @ sk_D_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('103',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('106',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = sk_D_2 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['95','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( sk_C_2 = sk_D_2 ) ),
    inference('sup-',[status(thm)],['94','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('112',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( ( k2_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('114',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_1 @ sk_D_2 @ ( sk_B @ ( k1_relat_1 @ sk_D_2 ) ) ) )
    | ( sk_C_2 = sk_D_2 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('118',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['101','102'])).

thf('120',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('122',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( ( k1_relat_1 @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('124',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X1 ) )
        = X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('125',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D_2 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D_2 ) ) ) @ k1_xboole_0 )
    | ( sk_C_2 = sk_D_2 )
    | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D_2 ) )
      = sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['101','102'])).

thf('128',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D_2 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D_2 ) ) ) @ k1_xboole_0 )
    | ( sk_C_2 = sk_D_2 )
    | ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D_2 ) )
      = sk_D_2 ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('131',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( sk_B @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('132',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_B @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('138',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( sk_B @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('139',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['136','141'])).

thf('143',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('147',plain,
    ( ( sk_B @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('152',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['149','154'])).

thf('156',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D_2 ) )
      = sk_D_2 )
    | ( sk_C_2 = sk_D_2 ) ),
    inference(clc,[status(thm)],['128','155'])).

thf('157',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_D_2 )
    | ( sk_C_2 = sk_D_2 )
    | ( sk_C_2 = sk_D_2 ) ),
    inference('sup+',[status(thm)],['122','156'])).

thf('158',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( ( k6_relat_1 @ k1_xboole_0 )
      = sk_D_2 ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( sk_C_2 = sk_D_2 )
    | ( sk_C_2 = sk_D_2 )
    | ( sk_C_2 = sk_D_2 ) ),
    inference('sup+',[status(thm)],['93','158'])).

thf('160',plain,(
    sk_C_2 = sk_D_2 ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('162',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('165',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_C_2 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('167',plain,(
    r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference(simpl_trail,[status(thm)],['165','166'])).

thf('168',plain,(
    $false ),
    inference(demod,[status(thm)],['42','160','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bq2a3JFWyX
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:38:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.07/1.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.26  % Solved by: fo/fo7.sh
% 1.07/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.26  % done 1776 iterations in 0.801s
% 1.07/1.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.26  % SZS output start Refutation
% 1.07/1.26  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.07/1.26  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.07/1.26  thf(sk_B_type, type, sk_B: $i > $i).
% 1.07/1.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.26  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 1.07/1.26  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.07/1.26  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.26  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.07/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.26  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.26  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.07/1.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.26  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.07/1.26  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.07/1.26  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.07/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.26  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.07/1.26  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.07/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.26  thf(t142_funct_2, conjecture,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.26         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.26       ( ![D:$i]:
% 1.07/1.26         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.07/1.26             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.26           ( ( r1_partfun1 @ C @ D ) =>
% 1.07/1.26             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.07/1.26               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 1.07/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.26    (~( ![A:$i,B:$i,C:$i]:
% 1.07/1.26        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.26            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.26          ( ![D:$i]:
% 1.07/1.26            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.07/1.26                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.26              ( ( r1_partfun1 @ C @ D ) =>
% 1.07/1.26                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.07/1.26                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 1.07/1.26    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 1.07/1.26  thf('0', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('1', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.07/1.26      inference('split', [status(esa)], ['0'])).
% 1.07/1.26  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('3', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_D_2))
% 1.07/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.26  thf('4', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('5', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(cc5_funct_2, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.07/1.26       ( ![C:$i]:
% 1.07/1.26         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.07/1.26             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.07/1.26  thf('6', plain,
% 1.07/1.26      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.07/1.26          | (v1_partfun1 @ X41 @ X42)
% 1.07/1.26          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 1.07/1.26          | ~ (v1_funct_1 @ X41)
% 1.07/1.26          | (v1_xboole_0 @ X43))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.07/1.26  thf('7', plain,
% 1.07/1.26      (((v1_xboole_0 @ sk_B_1)
% 1.07/1.26        | ~ (v1_funct_1 @ sk_D_2)
% 1.07/1.26        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1)
% 1.07/1.26        | (v1_partfun1 @ sk_D_2 @ sk_A))),
% 1.07/1.26      inference('sup-', [status(thm)], ['5', '6'])).
% 1.07/1.26  thf('8', plain, ((v1_funct_1 @ sk_D_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('9', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B_1)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('10', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D_2 @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.07/1.26  thf('11', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(t148_partfun1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( ( v1_funct_1 @ C ) & 
% 1.07/1.26         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.26       ( ![D:$i]:
% 1.07/1.26         ( ( ( v1_funct_1 @ D ) & 
% 1.07/1.26             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.26           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 1.07/1.26               ( r1_partfun1 @ C @ D ) ) =>
% 1.07/1.26             ( ( C ) = ( D ) ) ) ) ) ))).
% 1.07/1.26  thf('12', plain,
% 1.07/1.26      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X44)
% 1.07/1.26          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.07/1.26          | ((X47) = (X44))
% 1.07/1.26          | ~ (r1_partfun1 @ X47 @ X44)
% 1.07/1.26          | ~ (v1_partfun1 @ X44 @ X45)
% 1.07/1.26          | ~ (v1_partfun1 @ X47 @ X45)
% 1.07/1.26          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.07/1.26          | ~ (v1_funct_1 @ X47))),
% 1.07/1.26      inference('cnf', [status(esa)], [t148_partfun1])).
% 1.07/1.26  thf('13', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.07/1.26          | ~ (v1_partfun1 @ X0 @ sk_A)
% 1.07/1.26          | ~ (v1_partfun1 @ sk_D_2 @ sk_A)
% 1.07/1.26          | ~ (r1_partfun1 @ X0 @ sk_D_2)
% 1.07/1.26          | ((X0) = (sk_D_2))
% 1.07/1.26          | ~ (v1_funct_1 @ sk_D_2))),
% 1.07/1.26      inference('sup-', [status(thm)], ['11', '12'])).
% 1.07/1.26  thf('14', plain, ((v1_funct_1 @ sk_D_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('15', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.07/1.26          | ~ (v1_partfun1 @ X0 @ sk_A)
% 1.07/1.26          | ~ (v1_partfun1 @ sk_D_2 @ sk_A)
% 1.07/1.26          | ~ (r1_partfun1 @ X0 @ sk_D_2)
% 1.07/1.26          | ((X0) = (sk_D_2)))),
% 1.07/1.26      inference('demod', [status(thm)], ['13', '14'])).
% 1.07/1.26  thf('16', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((v1_xboole_0 @ sk_B_1)
% 1.07/1.26          | ((X0) = (sk_D_2))
% 1.07/1.26          | ~ (r1_partfun1 @ X0 @ sk_D_2)
% 1.07/1.26          | ~ (v1_partfun1 @ X0 @ sk_A)
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.07/1.26          | ~ (v1_funct_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['10', '15'])).
% 1.07/1.26  thf('17', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ sk_C_2)
% 1.07/1.26        | ~ (v1_partfun1 @ sk_C_2 @ sk_A)
% 1.07/1.26        | ~ (r1_partfun1 @ sk_C_2 @ sk_D_2)
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | (v1_xboole_0 @ sk_B_1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['4', '16'])).
% 1.07/1.26  thf('18', plain, ((v1_funct_1 @ sk_C_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('19', plain, ((r1_partfun1 @ sk_C_2 @ sk_D_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('20', plain,
% 1.07/1.26      ((~ (v1_partfun1 @ sk_C_2 @ sk_A)
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | (v1_xboole_0 @ sk_B_1))),
% 1.07/1.26      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.07/1.26  thf('21', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('22', plain,
% 1.07/1.26      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.07/1.26          | (v1_partfun1 @ X41 @ X42)
% 1.07/1.26          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 1.07/1.26          | ~ (v1_funct_1 @ X41)
% 1.07/1.26          | (v1_xboole_0 @ X43))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.07/1.26  thf('23', plain,
% 1.07/1.26      (((v1_xboole_0 @ sk_B_1)
% 1.07/1.26        | ~ (v1_funct_1 @ sk_C_2)
% 1.07/1.26        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)
% 1.07/1.26        | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 1.07/1.26      inference('sup-', [status(thm)], ['21', '22'])).
% 1.07/1.26  thf('24', plain, ((v1_funct_1 @ sk_C_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('25', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('26', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_C_2 @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.07/1.26  thf('27', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('clc', [status(thm)], ['20', '26'])).
% 1.07/1.26  thf(l13_xboole_0, axiom,
% 1.07/1.26    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.07/1.26  thf('28', plain,
% 1.07/1.26      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.26      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.26  thf('29', plain, ((((sk_C_2) = (sk_D_2)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['27', '28'])).
% 1.07/1.26  thf('30', plain,
% 1.07/1.26      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.07/1.26      inference('split', [status(esa)], ['0'])).
% 1.07/1.26  thf('31', plain,
% 1.07/1.26      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_2) = (sk_D_2))))
% 1.07/1.26         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['29', '30'])).
% 1.07/1.26  thf('32', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.07/1.26      inference('simplify', [status(thm)], ['31'])).
% 1.07/1.26  thf('33', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('34', plain,
% 1.07/1.26      ((~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2))
% 1.07/1.26         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['32', '33'])).
% 1.07/1.26  thf('35', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(reflexivity_r2_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.26     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.26         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.26       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 1.07/1.26  thf('36', plain,
% 1.07/1.26      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.07/1.26         ((r2_relset_1 @ X37 @ X38 @ X39 @ X39)
% 1.07/1.26          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.07/1.26          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 1.07/1.26      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 1.07/1.26  thf('37', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.07/1.26      inference('condensation', [status(thm)], ['36'])).
% 1.07/1.26  thf('38', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 1.07/1.26      inference('sup-', [status(thm)], ['35', '37'])).
% 1.07/1.26  thf('39', plain, ((((sk_B_1) = (k1_xboole_0)))),
% 1.07/1.26      inference('demod', [status(thm)], ['34', '38'])).
% 1.07/1.26  thf('40', plain,
% 1.07/1.26      ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 1.07/1.26      inference('split', [status(esa)], ['0'])).
% 1.07/1.26  thf('41', plain, ((((sk_A) = (k1_xboole_0)))),
% 1.07/1.26      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 1.07/1.26  thf('42', plain, (~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_D_2)),
% 1.07/1.26      inference('simpl_trail', [status(thm)], ['3', '41'])).
% 1.07/1.26  thf(existence_m1_subset_1, axiom,
% 1.07/1.26    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 1.07/1.26  thf('43', plain, (![X1 : $i]: (m1_subset_1 @ (sk_B @ X1) @ X1)),
% 1.07/1.26      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.07/1.26  thf(t2_subset, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ A @ B ) =>
% 1.07/1.26       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.07/1.26  thf('44', plain,
% 1.07/1.26      (![X3 : $i, X4 : $i]:
% 1.07/1.26         ((r2_hidden @ X3 @ X4)
% 1.07/1.26          | (v1_xboole_0 @ X4)
% 1.07/1.26          | ~ (m1_subset_1 @ X3 @ X4))),
% 1.07/1.26      inference('cnf', [status(esa)], [t2_subset])).
% 1.07/1.26  thf('45', plain,
% 1.07/1.26      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['43', '44'])).
% 1.07/1.26  thf(d5_funct_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.26       ( ![B:$i]:
% 1.07/1.26         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.07/1.26           ( ![C:$i]:
% 1.07/1.26             ( ( r2_hidden @ C @ B ) <=>
% 1.07/1.26               ( ?[D:$i]:
% 1.07/1.26                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.07/1.26                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.07/1.26  thf('46', plain,
% 1.07/1.26      (![X19 : $i, X21 : $i, X23 : $i, X24 : $i]:
% 1.07/1.26         (((X21) != (k2_relat_1 @ X19))
% 1.07/1.26          | (r2_hidden @ X23 @ X21)
% 1.07/1.26          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X19))
% 1.07/1.26          | ((X23) != (k1_funct_1 @ X19 @ X24))
% 1.07/1.26          | ~ (v1_funct_1 @ X19)
% 1.07/1.26          | ~ (v1_relat_1 @ X19))),
% 1.07/1.26      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.07/1.26  thf('47', plain,
% 1.07/1.26      (![X19 : $i, X24 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X19)
% 1.07/1.26          | ~ (v1_funct_1 @ X19)
% 1.07/1.26          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X19))
% 1.07/1.26          | (r2_hidden @ (k1_funct_1 @ X19 @ X24) @ (k2_relat_1 @ X19)))),
% 1.07/1.26      inference('simplify', [status(thm)], ['46'])).
% 1.07/1.26  thf('48', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.07/1.26          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 1.07/1.26             (k2_relat_1 @ X0))
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['45', '47'])).
% 1.07/1.26  thf('49', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('clc', [status(thm)], ['20', '26'])).
% 1.07/1.26  thf('50', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(cc2_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.07/1.26  thf('51', plain,
% 1.07/1.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.26         ((v5_relat_1 @ X34 @ X36)
% 1.07/1.26          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.26  thf('52', plain, ((v5_relat_1 @ sk_C_2 @ sk_B_1)),
% 1.07/1.26      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.26  thf(d19_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ B ) =>
% 1.07/1.26       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.07/1.26  thf('53', plain,
% 1.07/1.26      (![X14 : $i, X15 : $i]:
% 1.07/1.26         (~ (v5_relat_1 @ X14 @ X15)
% 1.07/1.26          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 1.07/1.26          | ~ (v1_relat_1 @ X14))),
% 1.07/1.26      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.07/1.26  thf('54', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['52', '53'])).
% 1.07/1.26  thf('55', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(cc1_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( v1_relat_1 @ C ) ))).
% 1.07/1.26  thf('56', plain,
% 1.07/1.26      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.07/1.26         ((v1_relat_1 @ X31)
% 1.07/1.26          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.07/1.26  thf('57', plain, ((v1_relat_1 @ sk_C_2)),
% 1.07/1.26      inference('sup-', [status(thm)], ['55', '56'])).
% 1.07/1.26  thf('58', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 1.07/1.26      inference('demod', [status(thm)], ['54', '57'])).
% 1.07/1.26  thf(t3_subset, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.07/1.26  thf('59', plain,
% 1.07/1.26      (![X5 : $i, X7 : $i]:
% 1.07/1.26         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 1.07/1.26      inference('cnf', [status(esa)], [t3_subset])).
% 1.07/1.26  thf('60', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['58', '59'])).
% 1.07/1.26  thf(t5_subset, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.07/1.26          ( v1_xboole_0 @ C ) ) ))).
% 1.07/1.26  thf('61', plain,
% 1.07/1.26      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X11 @ X12)
% 1.07/1.26          | ~ (v1_xboole_0 @ X13)
% 1.07/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.07/1.26      inference('cnf', [status(esa)], [t5_subset])).
% 1.07/1.26  thf('62', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.07/1.26  thf('63', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (((sk_C_2) = (sk_D_2)) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['49', '62'])).
% 1.07/1.26  thf('64', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ sk_C_2)
% 1.07/1.26        | ~ (v1_funct_1 @ sk_C_2)
% 1.07/1.26        | (v1_xboole_0 @ (k1_relat_1 @ sk_C_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['48', '63'])).
% 1.07/1.26  thf('65', plain, ((v1_relat_1 @ sk_C_2)),
% 1.07/1.26      inference('sup-', [status(thm)], ['55', '56'])).
% 1.07/1.26  thf('66', plain, ((v1_funct_1 @ sk_C_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('67', plain,
% 1.07/1.26      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_2)) | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.07/1.26  thf('68', plain,
% 1.07/1.26      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.26      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.26  thf('69', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2)) | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['67', '68'])).
% 1.07/1.26  thf('70', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2)) | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['67', '68'])).
% 1.07/1.26  thf('71', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2)) | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['67', '68'])).
% 1.07/1.26  thf(t71_relat_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.07/1.26       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.07/1.26  thf('72', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 1.07/1.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.26  thf(t9_funct_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.26       ( ![B:$i]:
% 1.07/1.26         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.07/1.26           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.07/1.26               ( ![C:$i]:
% 1.07/1.26                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.07/1.26                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 1.07/1.26             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.07/1.26  thf('73', plain,
% 1.07/1.26      (![X27 : $i, X28 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X27)
% 1.07/1.26          | ~ (v1_funct_1 @ X27)
% 1.07/1.26          | ((X28) = (X27))
% 1.07/1.26          | (r2_hidden @ (sk_C_1 @ X27 @ X28) @ (k1_relat_1 @ X28))
% 1.07/1.26          | ((k1_relat_1 @ X28) != (k1_relat_1 @ X27))
% 1.07/1.26          | ~ (v1_funct_1 @ X28)
% 1.07/1.26          | ~ (v1_relat_1 @ X28))),
% 1.07/1.26      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.07/1.26  thf('74', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (((X0) != (k1_relat_1 @ X1))
% 1.07/1.26          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.07/1.26          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.07/1.26          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ X0)) @ 
% 1.07/1.26             (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.07/1.26          | ((k6_relat_1 @ X0) = (X1))
% 1.07/1.26          | ~ (v1_funct_1 @ X1)
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['72', '73'])).
% 1.07/1.26  thf(fc3_funct_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.07/1.26       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.07/1.26  thf('75', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.07/1.26  thf('76', plain, (![X26 : $i]: (v1_funct_1 @ (k6_relat_1 @ X26))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.07/1.26  thf('77', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 1.07/1.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.26  thf('78', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (((X0) != (k1_relat_1 @ X1))
% 1.07/1.26          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ X0)) @ X0)
% 1.07/1.26          | ((k6_relat_1 @ X0) = (X1))
% 1.07/1.26          | ~ (v1_funct_1 @ X1)
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 1.07/1.26  thf('79', plain,
% 1.07/1.26      (![X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X1)
% 1.07/1.26          | ~ (v1_funct_1 @ X1)
% 1.07/1.26          | ((k6_relat_1 @ (k1_relat_1 @ X1)) = (X1))
% 1.07/1.26          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ (k1_relat_1 @ X1))) @ 
% 1.07/1.26             (k1_relat_1 @ X1)))),
% 1.07/1.26      inference('simplify', [status(thm)], ['78'])).
% 1.07/1.26  thf('80', plain,
% 1.07/1.26      (((r2_hidden @ (sk_C_1 @ sk_C_2 @ (k6_relat_1 @ k1_xboole_0)) @ 
% 1.07/1.26         (k1_relat_1 @ sk_C_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ((k6_relat_1 @ (k1_relat_1 @ sk_C_2)) = (sk_C_2))
% 1.07/1.26        | ~ (v1_funct_1 @ sk_C_2)
% 1.07/1.26        | ~ (v1_relat_1 @ sk_C_2))),
% 1.07/1.26      inference('sup+', [status(thm)], ['71', '79'])).
% 1.07/1.26  thf('81', plain, ((v1_funct_1 @ sk_C_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('82', plain, ((v1_relat_1 @ sk_C_2)),
% 1.07/1.26      inference('sup-', [status(thm)], ['55', '56'])).
% 1.07/1.26  thf('83', plain,
% 1.07/1.26      (((r2_hidden @ (sk_C_1 @ sk_C_2 @ (k6_relat_1 @ k1_xboole_0)) @ 
% 1.07/1.26         (k1_relat_1 @ sk_C_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ((k6_relat_1 @ (k1_relat_1 @ sk_C_2)) = (sk_C_2)))),
% 1.07/1.26      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.07/1.26  thf(t7_ordinal1, axiom,
% 1.07/1.26    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.07/1.26  thf('84', plain,
% 1.07/1.26      (![X29 : $i, X30 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.07/1.26  thf('85', plain,
% 1.07/1.26      ((((k6_relat_1 @ (k1_relat_1 @ sk_C_2)) = (sk_C_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ~ (r1_tarski @ (k1_relat_1 @ sk_C_2) @ 
% 1.07/1.26             (sk_C_1 @ sk_C_2 @ (k6_relat_1 @ k1_xboole_0))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['83', '84'])).
% 1.07/1.26  thf('86', plain,
% 1.07/1.26      ((~ (r1_tarski @ k1_xboole_0 @ 
% 1.07/1.26           (sk_C_1 @ sk_C_2 @ (k6_relat_1 @ k1_xboole_0)))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ((k6_relat_1 @ (k1_relat_1 @ sk_C_2)) = (sk_C_2)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['70', '85'])).
% 1.07/1.26  thf(t4_subset_1, axiom,
% 1.07/1.26    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.07/1.26  thf('87', plain,
% 1.07/1.26      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 1.07/1.26      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.07/1.26  thf('88', plain,
% 1.07/1.26      (![X5 : $i, X6 : $i]:
% 1.07/1.26         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.07/1.26      inference('cnf', [status(esa)], [t3_subset])).
% 1.07/1.26  thf('89', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.07/1.26      inference('sup-', [status(thm)], ['87', '88'])).
% 1.07/1.26  thf('90', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ((k6_relat_1 @ (k1_relat_1 @ sk_C_2)) = (sk_C_2)))),
% 1.07/1.26      inference('demod', [status(thm)], ['86', '89'])).
% 1.07/1.26  thf('91', plain,
% 1.07/1.26      ((((k6_relat_1 @ (k1_relat_1 @ sk_C_2)) = (sk_C_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('simplify', [status(thm)], ['90'])).
% 1.07/1.26  thf('92', plain,
% 1.07/1.26      ((((k6_relat_1 @ k1_xboole_0) = (sk_C_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['69', '91'])).
% 1.07/1.26  thf('93', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2)) | ((k6_relat_1 @ k1_xboole_0) = (sk_C_2)))),
% 1.07/1.26      inference('simplify', [status(thm)], ['92'])).
% 1.07/1.26  thf('94', plain,
% 1.07/1.26      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['43', '44'])).
% 1.07/1.26  thf('95', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('clc', [status(thm)], ['20', '26'])).
% 1.07/1.26  thf('96', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('97', plain,
% 1.07/1.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.26         ((v5_relat_1 @ X34 @ X36)
% 1.07/1.26          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.26  thf('98', plain, ((v5_relat_1 @ sk_D_2 @ sk_B_1)),
% 1.07/1.26      inference('sup-', [status(thm)], ['96', '97'])).
% 1.07/1.26  thf('99', plain,
% 1.07/1.26      (![X14 : $i, X15 : $i]:
% 1.07/1.26         (~ (v5_relat_1 @ X14 @ X15)
% 1.07/1.26          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 1.07/1.26          | ~ (v1_relat_1 @ X14))),
% 1.07/1.26      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.07/1.26  thf('100', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B_1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['98', '99'])).
% 1.07/1.26  thf('101', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('102', plain,
% 1.07/1.26      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.07/1.26         ((v1_relat_1 @ X31)
% 1.07/1.26          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.07/1.26  thf('103', plain, ((v1_relat_1 @ sk_D_2)),
% 1.07/1.26      inference('sup-', [status(thm)], ['101', '102'])).
% 1.07/1.26  thf('104', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B_1)),
% 1.07/1.26      inference('demod', [status(thm)], ['100', '103'])).
% 1.07/1.26  thf('105', plain,
% 1.07/1.26      (![X5 : $i, X7 : $i]:
% 1.07/1.26         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 1.07/1.26      inference('cnf', [status(esa)], [t3_subset])).
% 1.07/1.26  thf('106', plain,
% 1.07/1.26      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['104', '105'])).
% 1.07/1.26  thf('107', plain,
% 1.07/1.26      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X11 @ X12)
% 1.07/1.26          | ~ (v1_xboole_0 @ X13)
% 1.07/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.07/1.26      inference('cnf', [status(esa)], [t5_subset])).
% 1.07/1.26  thf('108', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['106', '107'])).
% 1.07/1.26  thf('109', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (((sk_C_2) = (sk_D_2)) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['95', '108'])).
% 1.07/1.26  thf('110', plain,
% 1.07/1.26      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_2)) | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['94', '109'])).
% 1.07/1.26  thf('111', plain,
% 1.07/1.26      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.26      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.26  thf('112', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2)) | ((k2_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['110', '111'])).
% 1.07/1.26  thf('113', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.07/1.26          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 1.07/1.26             (k2_relat_1 @ X0))
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['45', '47'])).
% 1.07/1.26  thf('114', plain,
% 1.07/1.26      (![X29 : $i, X30 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.07/1.26  thf('115', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 1.07/1.26          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 1.07/1.26               (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['113', '114'])).
% 1.07/1.26  thf('116', plain,
% 1.07/1.26      ((~ (r1_tarski @ k1_xboole_0 @ 
% 1.07/1.26           (k1_funct_1 @ sk_D_2 @ (sk_B @ (k1_relat_1 @ sk_D_2))))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | (v1_xboole_0 @ (k1_relat_1 @ sk_D_2))
% 1.07/1.26        | ~ (v1_funct_1 @ sk_D_2)
% 1.07/1.26        | ~ (v1_relat_1 @ sk_D_2))),
% 1.07/1.26      inference('sup-', [status(thm)], ['112', '115'])).
% 1.07/1.26  thf('117', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.07/1.26      inference('sup-', [status(thm)], ['87', '88'])).
% 1.07/1.26  thf('118', plain, ((v1_funct_1 @ sk_D_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('119', plain, ((v1_relat_1 @ sk_D_2)),
% 1.07/1.26      inference('sup-', [status(thm)], ['101', '102'])).
% 1.07/1.26  thf('120', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2)) | (v1_xboole_0 @ (k1_relat_1 @ sk_D_2)))),
% 1.07/1.26      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 1.07/1.26  thf('121', plain,
% 1.07/1.26      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.26      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.26  thf('122', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2)) | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['120', '121'])).
% 1.07/1.26  thf('123', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2)) | ((k1_relat_1 @ sk_D_2) = (k1_xboole_0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['120', '121'])).
% 1.07/1.26  thf('124', plain,
% 1.07/1.26      (![X1 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X1)
% 1.07/1.26          | ~ (v1_funct_1 @ X1)
% 1.07/1.26          | ((k6_relat_1 @ (k1_relat_1 @ X1)) = (X1))
% 1.07/1.26          | (r2_hidden @ (sk_C_1 @ X1 @ (k6_relat_1 @ (k1_relat_1 @ X1))) @ 
% 1.07/1.26             (k1_relat_1 @ X1)))),
% 1.07/1.26      inference('simplify', [status(thm)], ['78'])).
% 1.07/1.26  thf('125', plain,
% 1.07/1.26      (((r2_hidden @ 
% 1.07/1.26         (sk_C_1 @ sk_D_2 @ (k6_relat_1 @ (k1_relat_1 @ sk_D_2))) @ k1_xboole_0)
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ((k6_relat_1 @ (k1_relat_1 @ sk_D_2)) = (sk_D_2))
% 1.07/1.26        | ~ (v1_funct_1 @ sk_D_2)
% 1.07/1.26        | ~ (v1_relat_1 @ sk_D_2))),
% 1.07/1.26      inference('sup+', [status(thm)], ['123', '124'])).
% 1.07/1.26  thf('126', plain, ((v1_funct_1 @ sk_D_2)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('127', plain, ((v1_relat_1 @ sk_D_2)),
% 1.07/1.26      inference('sup-', [status(thm)], ['101', '102'])).
% 1.07/1.26  thf('128', plain,
% 1.07/1.26      (((r2_hidden @ 
% 1.07/1.26         (sk_C_1 @ sk_D_2 @ (k6_relat_1 @ (k1_relat_1 @ sk_D_2))) @ k1_xboole_0)
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ((k6_relat_1 @ (k1_relat_1 @ sk_D_2)) = (sk_D_2)))),
% 1.07/1.26      inference('demod', [status(thm)], ['125', '126', '127'])).
% 1.07/1.26  thf('129', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.07/1.26      inference('sup-', [status(thm)], ['87', '88'])).
% 1.07/1.26  thf('130', plain,
% 1.07/1.26      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['43', '44'])).
% 1.07/1.26  thf('131', plain, (![X1 : $i]: (m1_subset_1 @ (sk_B @ X1) @ X1)),
% 1.07/1.26      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.07/1.26  thf(t4_subset, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.07/1.26       ( m1_subset_1 @ A @ C ) ))).
% 1.07/1.26  thf('132', plain,
% 1.07/1.26      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X8 @ X9)
% 1.07/1.26          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 1.07/1.26          | (m1_subset_1 @ X8 @ X10))),
% 1.07/1.26      inference('cnf', [status(esa)], [t4_subset])).
% 1.07/1.26  thf('133', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((m1_subset_1 @ X1 @ X0)
% 1.07/1.26          | ~ (r2_hidden @ X1 @ (sk_B @ (k1_zfmisc_1 @ X0))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['131', '132'])).
% 1.07/1.26  thf('134', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((v1_xboole_0 @ (sk_B @ (k1_zfmisc_1 @ X0)))
% 1.07/1.26          | (m1_subset_1 @ (sk_B @ (sk_B @ (k1_zfmisc_1 @ X0))) @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['130', '133'])).
% 1.07/1.26  thf('135', plain,
% 1.07/1.26      (![X3 : $i, X4 : $i]:
% 1.07/1.26         ((r2_hidden @ X3 @ X4)
% 1.07/1.26          | (v1_xboole_0 @ X4)
% 1.07/1.26          | ~ (m1_subset_1 @ X3 @ X4))),
% 1.07/1.26      inference('cnf', [status(esa)], [t2_subset])).
% 1.07/1.26  thf('136', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((v1_xboole_0 @ (sk_B @ (k1_zfmisc_1 @ X0)))
% 1.07/1.26          | (v1_xboole_0 @ X0)
% 1.07/1.26          | (r2_hidden @ (sk_B @ (sk_B @ (k1_zfmisc_1 @ X0))) @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['134', '135'])).
% 1.07/1.26  thf('137', plain,
% 1.07/1.26      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['43', '44'])).
% 1.07/1.26  thf('138', plain, (![X1 : $i]: (m1_subset_1 @ (sk_B @ X1) @ X1)),
% 1.07/1.26      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.07/1.26  thf('139', plain,
% 1.07/1.26      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X11 @ X12)
% 1.07/1.26          | ~ (v1_xboole_0 @ X13)
% 1.07/1.26          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.07/1.26      inference('cnf', [status(esa)], [t5_subset])).
% 1.07/1.26  thf('140', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_xboole_0 @ X0)
% 1.07/1.26          | ~ (r2_hidden @ X1 @ (sk_B @ (k1_zfmisc_1 @ X0))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['138', '139'])).
% 1.07/1.26  thf('141', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((v1_xboole_0 @ (sk_B @ (k1_zfmisc_1 @ X0))) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['137', '140'])).
% 1.07/1.26  thf('142', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((r2_hidden @ (sk_B @ (sk_B @ (k1_zfmisc_1 @ X0))) @ X0)
% 1.07/1.26          | (v1_xboole_0 @ (sk_B @ (k1_zfmisc_1 @ X0))))),
% 1.07/1.26      inference('clc', [status(thm)], ['136', '141'])).
% 1.07/1.26  thf('143', plain,
% 1.07/1.26      (![X29 : $i, X30 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.07/1.26  thf('144', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((v1_xboole_0 @ (sk_B @ (k1_zfmisc_1 @ X0)))
% 1.07/1.26          | ~ (r1_tarski @ X0 @ (sk_B @ (sk_B @ (k1_zfmisc_1 @ X0)))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['142', '143'])).
% 1.07/1.26  thf('145', plain, ((v1_xboole_0 @ (sk_B @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['129', '144'])).
% 1.07/1.26  thf('146', plain,
% 1.07/1.26      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.26      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.26  thf('147', plain, (((sk_B @ (k1_zfmisc_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['145', '146'])).
% 1.07/1.26  thf('148', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (v1_xboole_0 @ X0)
% 1.07/1.26          | ~ (r2_hidden @ X1 @ (sk_B @ (k1_zfmisc_1 @ X0))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['138', '139'])).
% 1.07/1.26  thf('149', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['147', '148'])).
% 1.07/1.26  thf('150', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.07/1.26      inference('sup-', [status(thm)], ['87', '88'])).
% 1.07/1.26  thf('151', plain,
% 1.07/1.26      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['43', '44'])).
% 1.07/1.26  thf('152', plain,
% 1.07/1.26      (![X29 : $i, X30 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.07/1.26  thf('153', plain,
% 1.07/1.26      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['151', '152'])).
% 1.07/1.26  thf('154', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.26      inference('sup-', [status(thm)], ['150', '153'])).
% 1.07/1.26  thf('155', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.07/1.26      inference('demod', [status(thm)], ['149', '154'])).
% 1.07/1.26  thf('156', plain,
% 1.07/1.26      ((((k6_relat_1 @ (k1_relat_1 @ sk_D_2)) = (sk_D_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('clc', [status(thm)], ['128', '155'])).
% 1.07/1.26  thf('157', plain,
% 1.07/1.26      ((((k6_relat_1 @ k1_xboole_0) = (sk_D_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2))
% 1.07/1.26        | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['122', '156'])).
% 1.07/1.26  thf('158', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2)) | ((k6_relat_1 @ k1_xboole_0) = (sk_D_2)))),
% 1.07/1.26      inference('simplify', [status(thm)], ['157'])).
% 1.07/1.26  thf('159', plain,
% 1.07/1.26      ((((sk_C_2) = (sk_D_2)) | ((sk_C_2) = (sk_D_2)) | ((sk_C_2) = (sk_D_2)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['93', '158'])).
% 1.07/1.26  thf('160', plain, (((sk_C_2) = (sk_D_2))),
% 1.07/1.26      inference('simplify', [status(thm)], ['159'])).
% 1.07/1.26  thf('161', plain,
% 1.07/1.26      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.07/1.26      inference('split', [status(esa)], ['0'])).
% 1.07/1.26  thf('162', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('163', plain,
% 1.07/1.26      (((m1_subset_1 @ sk_C_2 @ 
% 1.07/1.26         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.07/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.07/1.26      inference('sup+', [status(thm)], ['161', '162'])).
% 1.07/1.26  thf('164', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.07/1.26      inference('condensation', [status(thm)], ['36'])).
% 1.07/1.26  thf('165', plain,
% 1.07/1.26      (((r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_C_2))
% 1.07/1.26         <= ((((sk_A) = (k1_xboole_0))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['163', '164'])).
% 1.07/1.26  thf('166', plain, ((((sk_A) = (k1_xboole_0)))),
% 1.07/1.26      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 1.07/1.26  thf('167', plain, ((r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 1.07/1.26      inference('simpl_trail', [status(thm)], ['165', '166'])).
% 1.07/1.26  thf('168', plain, ($false),
% 1.07/1.26      inference('demod', [status(thm)], ['42', '160', '167'])).
% 1.07/1.26  
% 1.07/1.26  % SZS output end Refutation
% 1.07/1.26  
% 1.07/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
