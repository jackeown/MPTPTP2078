%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PARTyunR8R

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:54 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  192 (1095 expanded)
%              Number of leaves         :   48 ( 331 expanded)
%              Depth                    :   25
%              Number of atoms          : 1385 (12017 expanded)
%              Number of equality atoms :   29 ( 447 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t121_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X47 @ X46 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X47 @ X44 @ X45 ) @ X47 @ X44 @ X45 )
      | ( X46
       != ( k1_funct_2 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X44: $i,X45: $i,X47: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X47 @ X44 @ X45 ) @ X47 @ X44 @ X45 )
      | ~ ( r2_hidden @ X47 @ ( k1_funct_2 @ X45 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A ) @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A ) @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X39 = X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_C_1
    = ( sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_funct_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('15',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X30 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('23',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( ( k1_relat_1 @ X37 )
        = X40 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_relat_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X39 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['13','30','31'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','24','27'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_partfun1 @ X31 @ X32 )
      | ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('36',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relset_1 @ X0 @ X1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relset_1 @ X0 @ X1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('56',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( v1_partfun1 @ X34 @ X35 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( v1_funct_1 @ X34 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('62',plain,(
    ! [X50: $i] :
      ( ( v1_funct_2 @ X50 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('63',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('65',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('66',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('69',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('77',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) ) )
      | ( v1_partfun1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','78'])).

thf('80',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( v1_partfun1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('90',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( zip_tseitin_1 @ X51 @ X52 @ X53 @ X54 )
      | ( r2_hidden @ X51 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['99'])).

thf('101',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','103'])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_1 @ D @ C @ B @ A ) )
       => ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('105',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( ( k1_relat_1 @ X59 )
       != X58 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X59 @ X60 @ X58 ) @ X59 @ X60 @ X58 )
      | ( zip_tseitin_2 @ X59 @ X60 @ X58 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('106',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X59 )
      | ~ ( v1_funct_1 @ X59 )
      | ( zip_tseitin_2 @ X59 @ X60 @ ( k1_relat_1 @ X59 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X59 @ X60 @ ( k1_relat_1 @ X59 ) ) @ X59 @ X60 @ ( k1_relat_1 @ X59 ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','106'])).

thf('108',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( v1_funct_2 @ X55 @ X57 @ X56 )
      | ~ ( zip_tseitin_2 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['89','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('112',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( v1_funct_2 @ sk_C_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ sk_C_1 @ sk_A @ X1 )
      | ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X1: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( v1_funct_2 @ sk_C_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','115'])).

thf('117',plain,(
    ! [X1: $i] :
      ( ( v1_funct_2 @ sk_C_1 @ sk_A @ X1 )
      | ( v1_partfun1 @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('119',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( v1_partfun1 @ X34 @ X35 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( v1_funct_1 @ X34 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ( v1_partfun1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_partfun1 @ sk_C_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','66'])).

thf('128',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('129',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('133',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('134',plain,
    ( ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['126','134'])).

thf('136',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('138',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('141',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['36','139','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['33','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PARTyunR8R
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:15:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.61/1.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.61/1.78  % Solved by: fo/fo7.sh
% 1.61/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.78  % done 1830 iterations in 1.326s
% 1.61/1.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.61/1.78  % SZS output start Refutation
% 1.61/1.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.61/1.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.61/1.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.61/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.78  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.61/1.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.61/1.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.61/1.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.61/1.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.61/1.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.61/1.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.61/1.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.61/1.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.61/1.78  thf(sk_B_type, type, sk_B: $i > $i).
% 1.61/1.78  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.61/1.78  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 1.61/1.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.61/1.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.61/1.78  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 1.61/1.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.61/1.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.61/1.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 1.61/1.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.61/1.78  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 1.61/1.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.61/1.78  thf(t121_funct_2, conjecture,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 1.61/1.78       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.61/1.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.61/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.78    (~( ![A:$i,B:$i,C:$i]:
% 1.61/1.78        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 1.61/1.78          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.61/1.78            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 1.61/1.78    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 1.61/1.78  thf('0', plain,
% 1.61/1.78      ((~ (v1_funct_1 @ sk_C_1)
% 1.61/1.78        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 1.61/1.78        | ~ (m1_subset_1 @ sk_C_1 @ 
% 1.61/1.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('1', plain,
% 1.61/1.78      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1))
% 1.61/1.78         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)))),
% 1.61/1.78      inference('split', [status(esa)], ['0'])).
% 1.61/1.78  thf('2', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf(d2_funct_2, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 1.61/1.78       ( ![D:$i]:
% 1.61/1.78         ( ( r2_hidden @ D @ C ) <=>
% 1.61/1.78           ( ?[E:$i]:
% 1.61/1.78             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 1.61/1.78               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 1.61/1.78               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 1.61/1.78  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.61/1.78  thf(zf_stmt_2, axiom,
% 1.61/1.78    (![E:$i,D:$i,B:$i,A:$i]:
% 1.61/1.78     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 1.61/1.78       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 1.61/1.78         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 1.61/1.78         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 1.61/1.78  thf(zf_stmt_3, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 1.61/1.78       ( ![D:$i]:
% 1.61/1.78         ( ( r2_hidden @ D @ C ) <=>
% 1.61/1.78           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 1.61/1.78  thf('3', plain,
% 1.61/1.78      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.61/1.78         (~ (r2_hidden @ X47 @ X46)
% 1.61/1.78          | (zip_tseitin_0 @ (sk_E_1 @ X47 @ X44 @ X45) @ X47 @ X44 @ X45)
% 1.61/1.78          | ((X46) != (k1_funct_2 @ X45 @ X44)))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.61/1.78  thf('4', plain,
% 1.61/1.78      (![X44 : $i, X45 : $i, X47 : $i]:
% 1.61/1.78         ((zip_tseitin_0 @ (sk_E_1 @ X47 @ X44 @ X45) @ X47 @ X44 @ X45)
% 1.61/1.78          | ~ (r2_hidden @ X47 @ (k1_funct_2 @ X45 @ X44)))),
% 1.61/1.78      inference('simplify', [status(thm)], ['3'])).
% 1.61/1.78  thf('5', plain,
% 1.61/1.78      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A) @ sk_C_1 @ sk_B_1 @ 
% 1.61/1.78        sk_A)),
% 1.61/1.78      inference('sup-', [status(thm)], ['2', '4'])).
% 1.61/1.78  thf('6', plain,
% 1.61/1.78      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A) @ sk_C_1 @ sk_B_1 @ 
% 1.61/1.78        sk_A)),
% 1.61/1.78      inference('sup-', [status(thm)], ['2', '4'])).
% 1.61/1.78  thf('7', plain,
% 1.61/1.78      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.61/1.78         (((X39) = (X37)) | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.61/1.78  thf('8', plain, (((sk_C_1) = (sk_E_1 @ sk_C_1 @ sk_B_1 @ sk_A))),
% 1.61/1.78      inference('sup-', [status(thm)], ['6', '7'])).
% 1.61/1.78  thf('9', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.61/1.78      inference('demod', [status(thm)], ['5', '8'])).
% 1.61/1.78  thf('10', plain,
% 1.61/1.78      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.61/1.78         ((v1_funct_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.61/1.78  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.61/1.78  thf('12', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 1.61/1.78      inference('split', [status(esa)], ['0'])).
% 1.61/1.78  thf('13', plain, (((v1_funct_1 @ sk_C_1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['11', '12'])).
% 1.61/1.78  thf('14', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.61/1.78      inference('demod', [status(thm)], ['5', '8'])).
% 1.61/1.78  thf('15', plain,
% 1.61/1.78      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.61/1.78         ((r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 1.61/1.78          | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.61/1.78  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['14', '15'])).
% 1.61/1.78  thf(d10_xboole_0, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.61/1.78  thf('17', plain,
% 1.61/1.78      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 1.61/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.78  thf('18', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.61/1.78      inference('simplify', [status(thm)], ['17'])).
% 1.61/1.78  thf(t11_relset_1, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( v1_relat_1 @ C ) =>
% 1.61/1.78       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.61/1.78           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.61/1.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.61/1.78  thf('19', plain,
% 1.61/1.78      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.61/1.78         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 1.61/1.78          | ~ (r1_tarski @ (k2_relat_1 @ X28) @ X30)
% 1.61/1.78          | (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.61/1.78          | ~ (v1_relat_1 @ X28))),
% 1.61/1.78      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.61/1.78  thf('20', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | (m1_subset_1 @ X0 @ 
% 1.61/1.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.61/1.78          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['18', '19'])).
% 1.61/1.78  thf('21', plain,
% 1.61/1.78      (((m1_subset_1 @ sk_C_1 @ 
% 1.61/1.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)))
% 1.61/1.78        | ~ (v1_relat_1 @ sk_C_1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['16', '20'])).
% 1.61/1.78  thf('22', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.61/1.78      inference('demod', [status(thm)], ['5', '8'])).
% 1.61/1.78  thf('23', plain,
% 1.61/1.78      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.61/1.78         (((k1_relat_1 @ X37) = (X40))
% 1.61/1.78          | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.61/1.78  thf('24', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.61/1.78      inference('sup-', [status(thm)], ['22', '23'])).
% 1.61/1.78  thf('25', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.61/1.78      inference('demod', [status(thm)], ['5', '8'])).
% 1.61/1.78  thf('26', plain,
% 1.61/1.78      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.61/1.78         ((v1_relat_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X39 @ X38 @ X40))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.61/1.78  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['25', '26'])).
% 1.61/1.78  thf('28', plain,
% 1.61/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.61/1.78      inference('demod', [status(thm)], ['21', '24', '27'])).
% 1.61/1.78  thf('29', plain,
% 1.61/1.78      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 1.61/1.78         <= (~
% 1.61/1.78             ((m1_subset_1 @ sk_C_1 @ 
% 1.61/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))))),
% 1.61/1.78      inference('split', [status(esa)], ['0'])).
% 1.61/1.78  thf('30', plain,
% 1.61/1.78      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['28', '29'])).
% 1.61/1.78  thf('31', plain,
% 1.61/1.78      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)) | 
% 1.61/1.78       ~
% 1.61/1.78       ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))) | 
% 1.61/1.78       ~ ((v1_funct_1 @ sk_C_1))),
% 1.61/1.78      inference('split', [status(esa)], ['0'])).
% 1.61/1.78  thf('32', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1))),
% 1.61/1.78      inference('sat_resolution*', [status(thm)], ['13', '30', '31'])).
% 1.61/1.78  thf('33', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.61/1.78      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 1.61/1.78  thf('34', plain,
% 1.61/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.61/1.78      inference('demod', [status(thm)], ['21', '24', '27'])).
% 1.61/1.78  thf(cc1_funct_2, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.61/1.78       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 1.61/1.78         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 1.61/1.78  thf('35', plain,
% 1.61/1.78      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.61/1.78         (~ (v1_funct_1 @ X31)
% 1.61/1.78          | ~ (v1_partfun1 @ X31 @ X32)
% 1.61/1.78          | (v1_funct_2 @ X31 @ X32 @ X33)
% 1.61/1.78          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.61/1.78      inference('cnf', [status(esa)], [cc1_funct_2])).
% 1.61/1.78  thf('36', plain,
% 1.61/1.78      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 1.61/1.78        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78        | ~ (v1_funct_1 @ sk_C_1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['34', '35'])).
% 1.61/1.78  thf(d1_xboole_0, axiom,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.61/1.78  thf('37', plain,
% 1.61/1.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.61/1.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.61/1.78  thf('38', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 1.61/1.78      inference('simplify', [status(thm)], ['17'])).
% 1.61/1.78  thf(t3_subset, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.61/1.78  thf('39', plain,
% 1.61/1.78      (![X13 : $i, X15 : $i]:
% 1.61/1.78         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 1.61/1.78      inference('cnf', [status(esa)], [t3_subset])).
% 1.61/1.78  thf('40', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['38', '39'])).
% 1.61/1.78  thf(redefinition_k1_relset_1, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.61/1.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.61/1.78  thf('41', plain,
% 1.61/1.78      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.61/1.78         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 1.61/1.78          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.61/1.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.61/1.78  thf('42', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.61/1.78           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['40', '41'])).
% 1.61/1.78  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['38', '39'])).
% 1.61/1.78  thf(dt_k1_relset_1, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.61/1.78       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.61/1.78  thf('44', plain,
% 1.61/1.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.61/1.78         ((m1_subset_1 @ (k1_relset_1 @ X22 @ X23 @ X24) @ (k1_zfmisc_1 @ X22))
% 1.61/1.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.61/1.78      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 1.61/1.78  thf('45', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 1.61/1.78          (k1_zfmisc_1 @ X1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['43', '44'])).
% 1.61/1.78  thf('46', plain,
% 1.61/1.78      (![X13 : $i, X14 : $i]:
% 1.61/1.78         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t3_subset])).
% 1.61/1.78  thf('47', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (r1_tarski @ (k1_relset_1 @ X0 @ X1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 1.61/1.78      inference('sup-', [status(thm)], ['45', '46'])).
% 1.61/1.78  thf(d3_tarski, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( r1_tarski @ A @ B ) <=>
% 1.61/1.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.61/1.78  thf('48', plain,
% 1.61/1.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.61/1.78         (~ (r2_hidden @ X3 @ X4)
% 1.61/1.78          | (r2_hidden @ X3 @ X5)
% 1.61/1.78          | ~ (r1_tarski @ X4 @ X5))),
% 1.61/1.78      inference('cnf', [status(esa)], [d3_tarski])).
% 1.61/1.78  thf('49', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         ((r2_hidden @ X2 @ X0)
% 1.61/1.78          | ~ (r2_hidden @ X2 @ 
% 1.61/1.78               (k1_relset_1 @ X0 @ X1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 1.61/1.78      inference('sup-', [status(thm)], ['47', '48'])).
% 1.61/1.78  thf('50', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.61/1.78          | (r2_hidden @ X2 @ X1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['42', '49'])).
% 1.61/1.78  thf('51', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((v1_xboole_0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.61/1.78          | (r2_hidden @ (sk_B @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['37', '50'])).
% 1.61/1.78  thf('52', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.61/1.78      inference('sup-', [status(thm)], ['22', '23'])).
% 1.61/1.78  thf(t3_funct_2, axiom,
% 1.61/1.78    (![A:$i]:
% 1.61/1.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.61/1.78       ( ( v1_funct_1 @ A ) & 
% 1.61/1.78         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.61/1.78         ( m1_subset_1 @
% 1.61/1.78           A @ 
% 1.61/1.78           ( k1_zfmisc_1 @
% 1.61/1.78             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.61/1.78  thf('53', plain,
% 1.61/1.78      (![X50 : $i]:
% 1.61/1.78         ((m1_subset_1 @ X50 @ 
% 1.61/1.78           (k1_zfmisc_1 @ 
% 1.61/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 1.61/1.78          | ~ (v1_funct_1 @ X50)
% 1.61/1.78          | ~ (v1_relat_1 @ X50))),
% 1.61/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.61/1.78  thf('54', plain,
% 1.61/1.78      (((m1_subset_1 @ sk_C_1 @ 
% 1.61/1.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))
% 1.61/1.78        | ~ (v1_relat_1 @ sk_C_1)
% 1.61/1.78        | ~ (v1_funct_1 @ sk_C_1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['52', '53'])).
% 1.61/1.78  thf('55', plain, ((v1_relat_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['25', '26'])).
% 1.61/1.78  thf('56', plain, ((v1_funct_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.61/1.78  thf('57', plain,
% 1.61/1.78      ((m1_subset_1 @ sk_C_1 @ 
% 1.61/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C_1))))),
% 1.61/1.78      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.61/1.78  thf(cc5_funct_2, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.61/1.78       ( ![C:$i]:
% 1.61/1.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.61/1.78           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.61/1.78             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.61/1.78  thf('58', plain,
% 1.61/1.78      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.61/1.78         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.61/1.78          | (v1_partfun1 @ X34 @ X35)
% 1.61/1.78          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 1.61/1.78          | ~ (v1_funct_1 @ X34)
% 1.61/1.78          | (v1_xboole_0 @ X36))),
% 1.61/1.78      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.61/1.78  thf('59', plain,
% 1.61/1.78      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 1.61/1.78        | ~ (v1_funct_1 @ sk_C_1)
% 1.61/1.78        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 1.61/1.78        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.61/1.78      inference('sup-', [status(thm)], ['57', '58'])).
% 1.61/1.78  thf('60', plain, ((v1_funct_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.61/1.78  thf('61', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.61/1.78      inference('sup-', [status(thm)], ['22', '23'])).
% 1.61/1.78  thf('62', plain,
% 1.61/1.78      (![X50 : $i]:
% 1.61/1.78         ((v1_funct_2 @ X50 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))
% 1.61/1.78          | ~ (v1_funct_1 @ X50)
% 1.61/1.78          | ~ (v1_relat_1 @ X50))),
% 1.61/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.61/1.78  thf('63', plain,
% 1.61/1.78      (((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))
% 1.61/1.78        | ~ (v1_relat_1 @ sk_C_1)
% 1.61/1.78        | ~ (v1_funct_1 @ sk_C_1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['61', '62'])).
% 1.61/1.78  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['25', '26'])).
% 1.61/1.78  thf('65', plain, ((v1_funct_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.61/1.78  thf('66', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 1.61/1.78      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.61/1.78  thf('67', plain,
% 1.61/1.78      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.61/1.78      inference('demod', [status(thm)], ['59', '60', '66'])).
% 1.61/1.78  thf('68', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['38', '39'])).
% 1.61/1.78  thf(cc4_relset_1, axiom,
% 1.61/1.78    (![A:$i,B:$i]:
% 1.61/1.78     ( ( v1_xboole_0 @ A ) =>
% 1.61/1.78       ( ![C:$i]:
% 1.61/1.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.61/1.78           ( v1_xboole_0 @ C ) ) ) ))).
% 1.61/1.78  thf('69', plain,
% 1.61/1.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X19)
% 1.61/1.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 1.61/1.78          | (v1_xboole_0 @ X20))),
% 1.61/1.78      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.61/1.78  thf('70', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['68', '69'])).
% 1.61/1.78  thf('71', plain,
% 1.61/1.78      (![X50 : $i]:
% 1.61/1.78         ((m1_subset_1 @ X50 @ 
% 1.61/1.78           (k1_zfmisc_1 @ 
% 1.61/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 1.61/1.78          | ~ (v1_funct_1 @ X50)
% 1.61/1.78          | ~ (v1_relat_1 @ X50))),
% 1.61/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.61/1.78  thf(t5_subset, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.61/1.78          ( v1_xboole_0 @ C ) ) ))).
% 1.61/1.78  thf('72', plain,
% 1.61/1.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.61/1.78         (~ (r2_hidden @ X16 @ X17)
% 1.61/1.78          | ~ (v1_xboole_0 @ X18)
% 1.61/1.78          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t5_subset])).
% 1.61/1.78  thf('73', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_funct_1 @ X0)
% 1.61/1.78          | ~ (v1_xboole_0 @ 
% 1.61/1.78               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.61/1.78          | ~ (r2_hidden @ X1 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['71', '72'])).
% 1.61/1.78  thf('74', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 1.61/1.78          | ~ (r2_hidden @ X1 @ X0)
% 1.61/1.78          | ~ (v1_funct_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['70', '73'])).
% 1.61/1.78  thf('75', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78          | ~ (v1_relat_1 @ sk_C_1)
% 1.61/1.78          | ~ (v1_funct_1 @ sk_C_1)
% 1.61/1.78          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['67', '74'])).
% 1.61/1.78  thf('76', plain, ((v1_relat_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['25', '26'])).
% 1.61/1.78  thf('77', plain, ((v1_funct_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.61/1.78  thf('78', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((v1_partfun1 @ sk_C_1 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.61/1.78      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.61/1.78  thf('79', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((v1_xboole_0 @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ X0)))
% 1.61/1.78          | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.61/1.78      inference('sup-', [status(thm)], ['51', '78'])).
% 1.61/1.78  thf('80', plain,
% 1.61/1.78      (![X4 : $i, X6 : $i]:
% 1.61/1.78         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.61/1.78      inference('cnf', [status(esa)], [d3_tarski])).
% 1.61/1.78  thf('81', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((v1_partfun1 @ sk_C_1 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.61/1.78      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.61/1.78  thf('82', plain,
% 1.61/1.78      (![X0 : $i]: ((r1_tarski @ sk_C_1 @ X0) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.61/1.78      inference('sup-', [status(thm)], ['80', '81'])).
% 1.61/1.78  thf('83', plain,
% 1.61/1.78      (![X4 : $i, X6 : $i]:
% 1.61/1.78         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.61/1.78      inference('cnf', [status(esa)], [d3_tarski])).
% 1.61/1.78  thf('84', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.61/1.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.61/1.78  thf('85', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['83', '84'])).
% 1.61/1.78  thf('86', plain,
% 1.61/1.78      (![X7 : $i, X9 : $i]:
% 1.61/1.78         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 1.61/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.61/1.78  thf('87', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['85', '86'])).
% 1.61/1.78  thf('88', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78          | ((sk_C_1) = (X0))
% 1.61/1.78          | ~ (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['82', '87'])).
% 1.61/1.78  thf('89', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.61/1.78      inference('sup-', [status(thm)], ['22', '23'])).
% 1.61/1.78  thf(t5_funct_2, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 1.61/1.78       ( ( ( ![D:$i]:
% 1.61/1.78             ( ( r2_hidden @ D @ A ) =>
% 1.61/1.78               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 1.61/1.78           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 1.61/1.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.61/1.78           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 1.61/1.78  thf(zf_stmt_4, axiom,
% 1.61/1.78    (![D:$i,C:$i,B:$i,A:$i]:
% 1.61/1.78     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 1.61/1.78       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 1.61/1.78  thf('90', plain,
% 1.61/1.78      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.61/1.78         ((zip_tseitin_1 @ X51 @ X52 @ X53 @ X54) | (r2_hidden @ X51 @ X54))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.61/1.78  thf('91', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['68', '69'])).
% 1.61/1.78  thf('92', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['83', '84'])).
% 1.61/1.78  thf('93', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['85', '86'])).
% 1.61/1.78  thf('94', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['92', '93'])).
% 1.61/1.78  thf('95', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X0)
% 1.61/1.78          | ~ (v1_xboole_0 @ X2)
% 1.61/1.78          | ((k2_zfmisc_1 @ X1 @ X0) = (X2)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['91', '94'])).
% 1.61/1.78  thf('96', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.61/1.78           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['40', '41'])).
% 1.61/1.78  thf('97', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 1.61/1.78          (k1_zfmisc_1 @ X1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['43', '44'])).
% 1.61/1.78  thf('98', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (m1_subset_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 1.61/1.78          (k1_zfmisc_1 @ X1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['96', '97'])).
% 1.61/1.78  thf('99', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         ((m1_subset_1 @ (k1_relat_1 @ X0) @ (k1_zfmisc_1 @ X1))
% 1.61/1.78          | ~ (v1_xboole_0 @ X0)
% 1.61/1.78          | ~ (v1_xboole_0 @ X2))),
% 1.61/1.78      inference('sup+', [status(thm)], ['95', '98'])).
% 1.61/1.78  thf('100', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((m1_subset_1 @ (k1_relat_1 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.61/1.78          | ~ (v1_xboole_0 @ X1))),
% 1.61/1.78      inference('condensation', [status(thm)], ['99'])).
% 1.61/1.78  thf('101', plain,
% 1.61/1.78      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.61/1.78         (~ (r2_hidden @ X16 @ X17)
% 1.61/1.78          | ~ (v1_xboole_0 @ X18)
% 1.61/1.78          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.61/1.78      inference('cnf', [status(esa)], [t5_subset])).
% 1.61/1.78  thf('102', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X1)
% 1.61/1.78          | ~ (v1_xboole_0 @ X0)
% 1.61/1.78          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X1)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['100', '101'])).
% 1.61/1.78  thf('103', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('condensation', [status(thm)], ['102'])).
% 1.61/1.78  thf('104', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.61/1.78         ((zip_tseitin_1 @ X1 @ X3 @ X2 @ (k1_relat_1 @ X0))
% 1.61/1.78          | ~ (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['90', '103'])).
% 1.61/1.78  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 1.61/1.78  thf(zf_stmt_6, axiom,
% 1.61/1.78    (![C:$i,B:$i,A:$i]:
% 1.61/1.78     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 1.61/1.78       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.61/1.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.61/1.78  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 1.61/1.78  thf(zf_stmt_8, axiom,
% 1.61/1.78    (![A:$i,B:$i,C:$i]:
% 1.61/1.78     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.61/1.78       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 1.61/1.78           ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 1.61/1.78         ( zip_tseitin_2 @ C @ B @ A ) ) ))).
% 1.61/1.78  thf('105', plain,
% 1.61/1.78      (![X58 : $i, X59 : $i, X60 : $i]:
% 1.61/1.78         (((k1_relat_1 @ X59) != (X58))
% 1.61/1.78          | ~ (zip_tseitin_1 @ (sk_D_1 @ X59 @ X60 @ X58) @ X59 @ X60 @ X58)
% 1.61/1.78          | (zip_tseitin_2 @ X59 @ X60 @ X58)
% 1.61/1.78          | ~ (v1_funct_1 @ X59)
% 1.61/1.78          | ~ (v1_relat_1 @ X59))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.61/1.78  thf('106', plain,
% 1.61/1.78      (![X59 : $i, X60 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X59)
% 1.61/1.78          | ~ (v1_funct_1 @ X59)
% 1.61/1.78          | (zip_tseitin_2 @ X59 @ X60 @ (k1_relat_1 @ X59))
% 1.61/1.78          | ~ (zip_tseitin_1 @ (sk_D_1 @ X59 @ X60 @ (k1_relat_1 @ X59)) @ 
% 1.61/1.78               X59 @ X60 @ (k1_relat_1 @ X59)))),
% 1.61/1.78      inference('simplify', [status(thm)], ['105'])).
% 1.61/1.78  thf('107', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X0)
% 1.61/1.78          | (zip_tseitin_2 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 1.61/1.78          | ~ (v1_funct_1 @ X0)
% 1.61/1.78          | ~ (v1_relat_1 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['104', '106'])).
% 1.61/1.78  thf('108', plain,
% 1.61/1.78      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.61/1.78         ((v1_funct_2 @ X55 @ X57 @ X56) | ~ (zip_tseitin_2 @ X55 @ X56 @ X57))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_6])).
% 1.61/1.78  thf('109', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_funct_1 @ X0)
% 1.61/1.78          | ~ (v1_xboole_0 @ X0)
% 1.61/1.78          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['107', '108'])).
% 1.61/1.78  thf('110', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((v1_funct_2 @ sk_C_1 @ sk_A @ X0)
% 1.61/1.78          | ~ (v1_xboole_0 @ sk_C_1)
% 1.61/1.78          | ~ (v1_funct_1 @ sk_C_1)
% 1.61/1.78          | ~ (v1_relat_1 @ sk_C_1))),
% 1.61/1.78      inference('sup+', [status(thm)], ['89', '109'])).
% 1.61/1.78  thf('111', plain, ((v1_funct_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.61/1.78  thf('112', plain, ((v1_relat_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['25', '26'])).
% 1.61/1.78  thf('113', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((v1_funct_2 @ sk_C_1 @ sk_A @ X0) | ~ (v1_xboole_0 @ sk_C_1))),
% 1.61/1.78      inference('demod', [status(thm)], ['110', '111', '112'])).
% 1.61/1.78  thf('114', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X0)
% 1.61/1.78          | ~ (v1_xboole_0 @ X0)
% 1.61/1.78          | (v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78          | (v1_funct_2 @ sk_C_1 @ sk_A @ X1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['88', '113'])).
% 1.61/1.78  thf('115', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         ((v1_funct_2 @ sk_C_1 @ sk_A @ X1)
% 1.61/1.78          | (v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78          | ~ (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('simplify', [status(thm)], ['114'])).
% 1.61/1.78  thf('116', plain,
% 1.61/1.78      (![X1 : $i]:
% 1.61/1.78         ((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78          | (v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78          | (v1_funct_2 @ sk_C_1 @ sk_A @ X1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['79', '115'])).
% 1.61/1.78  thf('117', plain,
% 1.61/1.78      (![X1 : $i]:
% 1.61/1.78         ((v1_funct_2 @ sk_C_1 @ sk_A @ X1) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.61/1.78      inference('simplify', [status(thm)], ['116'])).
% 1.61/1.78  thf('118', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('sup-', [status(thm)], ['83', '84'])).
% 1.61/1.78  thf('119', plain,
% 1.61/1.78      (![X13 : $i, X15 : $i]:
% 1.61/1.78         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 1.61/1.78      inference('cnf', [status(esa)], [t3_subset])).
% 1.61/1.78  thf('120', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['118', '119'])).
% 1.61/1.78  thf('121', plain,
% 1.61/1.78      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.61/1.78         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.61/1.78          | (v1_partfun1 @ X34 @ X35)
% 1.61/1.78          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 1.61/1.78          | ~ (v1_funct_1 @ X34)
% 1.61/1.78          | (v1_xboole_0 @ X36))),
% 1.61/1.78      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.61/1.78  thf('122', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X2)
% 1.61/1.78          | (v1_xboole_0 @ X0)
% 1.61/1.78          | ~ (v1_funct_1 @ X2)
% 1.61/1.78          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 1.61/1.78          | (v1_partfun1 @ X2 @ X1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['120', '121'])).
% 1.61/1.78  thf('123', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78          | (v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78          | ~ (v1_funct_1 @ sk_C_1)
% 1.61/1.78          | (v1_xboole_0 @ X0)
% 1.61/1.78          | ~ (v1_xboole_0 @ sk_C_1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['117', '122'])).
% 1.61/1.78  thf('124', plain, ((v1_funct_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.61/1.78  thf('125', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         ((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78          | (v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78          | (v1_xboole_0 @ X0)
% 1.61/1.78          | ~ (v1_xboole_0 @ sk_C_1))),
% 1.61/1.78      inference('demod', [status(thm)], ['123', '124'])).
% 1.61/1.78  thf('126', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ sk_C_1)
% 1.61/1.78          | (v1_xboole_0 @ X0)
% 1.61/1.78          | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.61/1.78      inference('simplify', [status(thm)], ['125'])).
% 1.61/1.78  thf('127', plain,
% 1.61/1.78      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 1.61/1.78      inference('demod', [status(thm)], ['59', '60', '66'])).
% 1.61/1.78  thf('128', plain,
% 1.61/1.78      (![X50 : $i]:
% 1.61/1.78         ((m1_subset_1 @ X50 @ 
% 1.61/1.78           (k1_zfmisc_1 @ 
% 1.61/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 1.61/1.78          | ~ (v1_funct_1 @ X50)
% 1.61/1.78          | ~ (v1_relat_1 @ X50))),
% 1.61/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.61/1.78  thf('129', plain,
% 1.61/1.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.61/1.78         (~ (v1_xboole_0 @ X19)
% 1.61/1.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 1.61/1.78          | (v1_xboole_0 @ X20))),
% 1.61/1.78      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.61/1.78  thf('130', plain,
% 1.61/1.78      (![X0 : $i]:
% 1.61/1.78         (~ (v1_relat_1 @ X0)
% 1.61/1.78          | ~ (v1_funct_1 @ X0)
% 1.61/1.78          | (v1_xboole_0 @ X0)
% 1.61/1.78          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 1.61/1.78      inference('sup-', [status(thm)], ['128', '129'])).
% 1.61/1.78  thf('131', plain,
% 1.61/1.78      (((v1_partfun1 @ sk_C_1 @ sk_A)
% 1.61/1.78        | (v1_xboole_0 @ sk_C_1)
% 1.61/1.78        | ~ (v1_funct_1 @ sk_C_1)
% 1.61/1.78        | ~ (v1_relat_1 @ sk_C_1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['127', '130'])).
% 1.61/1.78  thf('132', plain, ((v1_funct_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.61/1.78  thf('133', plain, ((v1_relat_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['25', '26'])).
% 1.61/1.78  thf('134', plain, (((v1_partfun1 @ sk_C_1 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 1.61/1.78      inference('demod', [status(thm)], ['131', '132', '133'])).
% 1.61/1.78  thf('135', plain,
% 1.61/1.78      (![X0 : $i]: ((v1_partfun1 @ sk_C_1 @ sk_A) | (v1_xboole_0 @ X0))),
% 1.61/1.78      inference('clc', [status(thm)], ['126', '134'])).
% 1.61/1.78  thf('136', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.61/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.78  thf('137', plain,
% 1.61/1.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.61/1.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.61/1.78  thf('138', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 1.61/1.78      inference('sup-', [status(thm)], ['136', '137'])).
% 1.61/1.78  thf('139', plain, ((v1_partfun1 @ sk_C_1 @ sk_A)),
% 1.61/1.78      inference('sup-', [status(thm)], ['135', '138'])).
% 1.61/1.78  thf('140', plain, ((v1_funct_1 @ sk_C_1)),
% 1.61/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.61/1.78  thf('141', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.61/1.78      inference('demod', [status(thm)], ['36', '139', '140'])).
% 1.61/1.78  thf('142', plain, ($false), inference('demod', [status(thm)], ['33', '141'])).
% 1.61/1.78  
% 1.61/1.78  % SZS output end Refutation
% 1.61/1.78  
% 1.61/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
