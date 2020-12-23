%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0UW8aNzrTM

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:48 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 258 expanded)
%              Number of leaves         :   42 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          :  908 (3019 expanded)
%              Number of equality atoms :   49 (  74 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('17',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('22',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','20','21'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('24',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['12','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

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

thf('26',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) @ X12 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X15: $i] :
      ( ( ( k2_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['36','44','45','46'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(s3_funct_1__e9_44_1__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('51',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('52',plain,(
    ! [X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('58',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('60',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50','58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k1_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('66',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X35 ) ) )
      | ( v1_partfun1 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_partfun1 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf(fc1_wellord2,axiom,
    ( ( v1_xboole_0 @ ( k1_wellord2 @ k1_xboole_0 ) )
    & ( v1_relat_1 @ ( k1_wellord2 @ k1_xboole_0 ) ) )).

thf('69',plain,(
    v1_xboole_0 @ ( k1_wellord2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[fc1_wellord2])).

thf(fc2_wellord2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_relat_1 @ ( k1_wellord2 @ A ) )
        & ~ ( v1_xboole_0 @ ( k1_wellord2 @ A ) ) ) ) )).

thf('70',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_wellord2 @ X29 ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_wellord2])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_partfun1 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['68','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('76',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_partfun1 @ X30 @ X31 )
      | ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('77',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_partfun1 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_partfun1 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('81',plain,(
    ~ ( v1_partfun1 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['24','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0UW8aNzrTM
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:32:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 290 iterations in 0.286s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.50/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.50/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.50/0.73  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.50/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.50/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.50/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.50/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.73  thf(t4_funct_2, conjecture,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.50/0.73       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.50/0.73         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.50/0.73           ( m1_subset_1 @
% 0.50/0.73             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i,B:$i]:
% 0.50/0.73        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.50/0.73          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.50/0.73            ( ( v1_funct_1 @ B ) & 
% 0.50/0.73              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.50/0.73              ( m1_subset_1 @
% 0.50/0.73                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.50/0.73  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(t3_funct_2, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.73       ( ( v1_funct_1 @ A ) & 
% 0.50/0.73         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.50/0.73         ( m1_subset_1 @
% 0.50/0.73           A @ 
% 0.50/0.73           ( k1_zfmisc_1 @
% 0.50/0.73             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.50/0.73  thf('1', plain,
% 0.50/0.73      (![X44 : $i]:
% 0.50/0.73         ((m1_subset_1 @ X44 @ 
% 0.50/0.73           (k1_zfmisc_1 @ 
% 0.50/0.73            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))))
% 0.50/0.73          | ~ (v1_funct_1 @ X44)
% 0.50/0.73          | ~ (v1_relat_1 @ X44))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.50/0.73  thf(t14_relset_1, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.50/0.73       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.50/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.50/0.73  thf('2', plain,
% 0.50/0.73      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.50/0.73         (~ (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.50/0.73          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.50/0.73          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.50/0.73      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_funct_1 @ X0)
% 0.50/0.73          | (m1_subset_1 @ X0 @ 
% 0.50/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.50/0.73          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.73  thf('4', plain,
% 0.50/0.73      (((m1_subset_1 @ sk_B_1 @ 
% 0.50/0.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.50/0.73        | ~ (v1_funct_1 @ sk_B_1)
% 0.50/0.73        | ~ (v1_relat_1 @ sk_B_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['0', '3'])).
% 0.50/0.73  thf('5', plain, ((v1_funct_1 @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('6', plain, ((v1_relat_1 @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('7', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B_1 @ 
% 0.50/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.50/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.50/0.73  thf('8', plain,
% 0.50/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.50/0.73         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.50/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.50/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.50/0.73  thf('9', plain,
% 0.50/0.73      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 0.50/0.73         = (k1_relat_1 @ sk_B_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.50/0.73  thf(d1_funct_2, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.50/0.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.50/0.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.50/0.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_1, axiom,
% 0.50/0.73    (![C:$i,B:$i,A:$i]:
% 0.50/0.73     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.50/0.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.50/0.73  thf('10', plain,
% 0.50/0.73      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.50/0.73         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 0.50/0.73          | (v1_funct_2 @ X40 @ X38 @ X39)
% 0.50/0.73          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.50/0.73  thf('11', plain,
% 0.50/0.73      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.50/0.73        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.50/0.73        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf('12', plain,
% 0.50/0.73      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.50/0.73        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.50/0.73      inference('simplify', [status(thm)], ['11'])).
% 0.50/0.73  thf('13', plain,
% 0.50/0.73      ((~ (v1_funct_1 @ sk_B_1)
% 0.50/0.73        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.50/0.73        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.50/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('14', plain,
% 0.50/0.73      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.50/0.73         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.50/0.73      inference('split', [status(esa)], ['13'])).
% 0.50/0.73  thf('15', plain, ((v1_funct_1 @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('16', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 0.50/0.73      inference('split', [status(esa)], ['13'])).
% 0.50/0.73  thf('17', plain, (((v1_funct_1 @ sk_B_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.50/0.73  thf('18', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B_1 @ 
% 0.50/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.50/0.73  thf('19', plain,
% 0.50/0.73      ((~ (m1_subset_1 @ sk_B_1 @ 
% 0.50/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.50/0.73         <= (~
% 0.50/0.73             ((m1_subset_1 @ sk_B_1 @ 
% 0.50/0.73               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 0.50/0.73      inference('split', [status(esa)], ['13'])).
% 0.50/0.73  thf('20', plain,
% 0.50/0.73      (((m1_subset_1 @ sk_B_1 @ 
% 0.50/0.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.73  thf('21', plain,
% 0.50/0.73      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.50/0.73       ~
% 0.50/0.73       ((m1_subset_1 @ sk_B_1 @ 
% 0.50/0.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 0.50/0.73       ~ ((v1_funct_1 @ sk_B_1))),
% 0.50/0.73      inference('split', [status(esa)], ['13'])).
% 0.50/0.73  thf('22', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.50/0.73      inference('sat_resolution*', [status(thm)], ['17', '20', '21'])).
% 0.50/0.73  thf('23', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.50/0.73      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 0.50/0.73  thf('24', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.50/0.73      inference('clc', [status(thm)], ['12', '23'])).
% 0.50/0.73  thf('25', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B_1 @ 
% 0.50/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.50/0.73  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.50/0.73  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.50/0.73  thf(zf_stmt_4, axiom,
% 0.50/0.73    (![B:$i,A:$i]:
% 0.50/0.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.73       ( zip_tseitin_0 @ B @ A ) ))).
% 0.50/0.73  thf(zf_stmt_5, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.50/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.50/0.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.50/0.73  thf('26', plain,
% 0.50/0.73      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.50/0.73         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.50/0.73          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.50/0.73          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.50/0.73  thf('27', plain,
% 0.50/0.73      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.50/0.73        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.73  thf('28', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('29', plain,
% 0.50/0.73      (![X36 : $i, X37 : $i]:
% 0.50/0.73         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.50/0.73  thf(t3_xboole_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.50/0.73  thf('30', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.50/0.73  thf('31', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (r1_tarski @ X1 @ X0)
% 0.50/0.73          | (zip_tseitin_0 @ X0 @ X2)
% 0.50/0.73          | ((X1) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.50/0.73  thf('32', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (((k2_relat_1 @ sk_B_1) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_A @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['28', '31'])).
% 0.50/0.73  thf('33', plain,
% 0.50/0.73      (![X44 : $i]:
% 0.50/0.73         ((m1_subset_1 @ X44 @ 
% 0.50/0.73           (k1_zfmisc_1 @ 
% 0.50/0.73            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))))
% 0.50/0.73          | ~ (v1_funct_1 @ X44)
% 0.50/0.73          | ~ (v1_relat_1 @ X44))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.50/0.73  thf(t3_subset, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.73  thf('34', plain,
% 0.50/0.73      (![X5 : $i, X6 : $i]:
% 0.50/0.73         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.73  thf('35', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_funct_1 @ X0)
% 0.50/0.73          | (r1_tarski @ X0 @ 
% 0.50/0.73             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.50/0.73  thf('36', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((r1_tarski @ sk_B_1 @ 
% 0.50/0.73           (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0))
% 0.50/0.73          | (zip_tseitin_0 @ sk_A @ X0)
% 0.50/0.73          | ~ (v1_funct_1 @ sk_B_1)
% 0.50/0.73          | ~ (v1_relat_1 @ sk_B_1))),
% 0.50/0.73      inference('sup+', [status(thm)], ['32', '35'])).
% 0.50/0.73  thf(t194_relat_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.50/0.73  thf('37', plain,
% 0.50/0.73      (![X11 : $i, X12 : $i]:
% 0.50/0.73         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X11 @ X12)) @ X12)),
% 0.50/0.73      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.50/0.73  thf('38', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.50/0.73  thf('39', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.73  thf(t64_relat_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.50/0.73           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.73         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.73  thf('40', plain,
% 0.50/0.73      (![X15 : $i]:
% 0.50/0.73         (((k2_relat_1 @ X15) != (k1_xboole_0))
% 0.50/0.73          | ((X15) = (k1_xboole_0))
% 0.50/0.73          | ~ (v1_relat_1 @ X15))),
% 0.50/0.73      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.50/0.73  thf('41', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (((k1_xboole_0) != (k1_xboole_0))
% 0.50/0.73          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.50/0.73          | ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.50/0.73  thf(fc6_relat_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.50/0.73  thf('42', plain,
% 0.50/0.73      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.50/0.73  thf('43', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (((k1_xboole_0) != (k1_xboole_0))
% 0.50/0.73          | ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.50/0.73      inference('demod', [status(thm)], ['41', '42'])).
% 0.50/0.73  thf('44', plain,
% 0.50/0.73      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['43'])).
% 0.50/0.73  thf('45', plain, ((v1_funct_1 @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('46', plain, ((v1_relat_1 @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('47', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((r1_tarski @ sk_B_1 @ k1_xboole_0) | (zip_tseitin_0 @ sk_A @ X0))),
% 0.50/0.73      inference('demod', [status(thm)], ['36', '44', '45', '46'])).
% 0.50/0.73  thf(t25_relat_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( v1_relat_1 @ B ) =>
% 0.50/0.73           ( ( r1_tarski @ A @ B ) =>
% 0.50/0.73             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.50/0.73               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.50/0.73  thf('48', plain,
% 0.50/0.73      (![X13 : $i, X14 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X13)
% 0.50/0.73          | (r1_tarski @ (k1_relat_1 @ X14) @ (k1_relat_1 @ X13))
% 0.50/0.73          | ~ (r1_tarski @ X14 @ X13)
% 0.50/0.73          | ~ (v1_relat_1 @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.50/0.73  thf('49', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((zip_tseitin_0 @ sk_A @ X0)
% 0.50/0.73          | ~ (v1_relat_1 @ sk_B_1)
% 0.50/0.73          | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ (k1_relat_1 @ k1_xboole_0))
% 0.50/0.73          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.73  thf('50', plain, ((v1_relat_1 @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(s3_funct_1__e9_44_1__funct_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ?[B:$i]:
% 0.50/0.73       ( ( ![C:$i]:
% 0.50/0.73           ( ( r2_hidden @ C @ A ) =>
% 0.50/0.73             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.50/0.73         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.50/0.73         ( v1_relat_1 @ B ) ) ))).
% 0.50/0.73  thf('51', plain, (![X16 : $i]: ((k1_relat_1 @ (sk_B @ X16)) = (X16))),
% 0.50/0.73      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.50/0.73  thf('52', plain,
% 0.50/0.73      (![X15 : $i]:
% 0.50/0.73         (((k1_relat_1 @ X15) != (k1_xboole_0))
% 0.50/0.73          | ((X15) = (k1_xboole_0))
% 0.50/0.73          | ~ (v1_relat_1 @ X15))),
% 0.50/0.73      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.50/0.73  thf('53', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (((X0) != (k1_xboole_0))
% 0.50/0.73          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.50/0.73          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['51', '52'])).
% 0.50/0.73  thf('54', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B @ X16))),
% 0.50/0.73      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.50/0.73  thf('55', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.50/0.73      inference('demod', [status(thm)], ['53', '54'])).
% 0.50/0.73  thf('56', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['55'])).
% 0.50/0.73  thf('57', plain, (![X16 : $i]: ((k1_relat_1 @ (sk_B @ X16)) = (X16))),
% 0.50/0.73      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.50/0.73  thf('58', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['56', '57'])).
% 0.50/0.73  thf('59', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['55'])).
% 0.50/0.73  thf('60', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B @ X16))),
% 0.50/0.73      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.50/0.73  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.50/0.73      inference('sup+', [status(thm)], ['59', '60'])).
% 0.50/0.73  thf('62', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((zip_tseitin_0 @ sk_A @ X0)
% 0.50/0.73          | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0))),
% 0.50/0.73      inference('demod', [status(thm)], ['49', '50', '58', '61'])).
% 0.50/0.73  thf('63', plain,
% 0.50/0.73      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.50/0.73  thf('64', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((zip_tseitin_0 @ sk_A @ X0) | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['62', '63'])).
% 0.50/0.73  thf('65', plain,
% 0.50/0.73      (![X44 : $i]:
% 0.50/0.73         ((m1_subset_1 @ X44 @ 
% 0.50/0.73           (k1_zfmisc_1 @ 
% 0.50/0.73            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))))
% 0.50/0.73          | ~ (v1_funct_1 @ X44)
% 0.50/0.73          | ~ (v1_relat_1 @ X44))),
% 0.50/0.73      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.50/0.73  thf(cc1_partfun1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( v1_xboole_0 @ A ) =>
% 0.50/0.73       ( ![C:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.73           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.50/0.73  thf('66', plain,
% 0.50/0.73      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ X33)
% 0.50/0.73          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X35)))
% 0.50/0.73          | (v1_partfun1 @ X34 @ X33))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.50/0.73  thf('67', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X0)
% 0.50/0.73          | ~ (v1_funct_1 @ X0)
% 0.50/0.73          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.50/0.73          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['65', '66'])).
% 0.50/0.73  thf('68', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.50/0.73          | (zip_tseitin_0 @ sk_A @ X0)
% 0.50/0.73          | (v1_partfun1 @ sk_B_1 @ (k1_relat_1 @ sk_B_1))
% 0.50/0.73          | ~ (v1_funct_1 @ sk_B_1)
% 0.50/0.73          | ~ (v1_relat_1 @ sk_B_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['64', '67'])).
% 0.50/0.73  thf(fc1_wellord2, axiom,
% 0.50/0.73    (( v1_xboole_0 @ ( k1_wellord2 @ k1_xboole_0 ) ) & 
% 0.50/0.73     ( v1_relat_1 @ ( k1_wellord2 @ k1_xboole_0 ) ))).
% 0.50/0.73  thf('69', plain, ((v1_xboole_0 @ (k1_wellord2 @ k1_xboole_0))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc1_wellord2])).
% 0.50/0.73  thf(fc2_wellord2, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.50/0.73       ( ( v1_relat_1 @ ( k1_wellord2 @ A ) ) & 
% 0.50/0.73         ( ~( v1_xboole_0 @ ( k1_wellord2 @ A ) ) ) ) ))).
% 0.50/0.73  thf('70', plain,
% 0.50/0.73      (![X29 : $i]:
% 0.50/0.73         (~ (v1_xboole_0 @ (k1_wellord2 @ X29)) | (v1_xboole_0 @ X29))),
% 0.50/0.73      inference('cnf', [status(esa)], [fc2_wellord2])).
% 0.50/0.73  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.50/0.73      inference('sup-', [status(thm)], ['69', '70'])).
% 0.50/0.73  thf('72', plain, ((v1_funct_1 @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('73', plain, ((v1_relat_1 @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('74', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((zip_tseitin_0 @ sk_A @ X0)
% 0.50/0.73          | (v1_partfun1 @ sk_B_1 @ (k1_relat_1 @ sk_B_1)))),
% 0.50/0.73      inference('demod', [status(thm)], ['68', '71', '72', '73'])).
% 0.50/0.73  thf('75', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_B_1 @ 
% 0.50/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.50/0.73      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.50/0.73  thf(cc1_funct_2, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.73       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.50/0.73         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.50/0.73  thf('76', plain,
% 0.50/0.73      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.50/0.73         (~ (v1_funct_1 @ X30)
% 0.50/0.73          | ~ (v1_partfun1 @ X30 @ X31)
% 0.50/0.73          | (v1_funct_2 @ X30 @ X31 @ X32)
% 0.50/0.73          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.50/0.73  thf('77', plain,
% 0.50/0.73      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.50/0.73        | ~ (v1_partfun1 @ sk_B_1 @ (k1_relat_1 @ sk_B_1))
% 0.50/0.73        | ~ (v1_funct_1 @ sk_B_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['75', '76'])).
% 0.50/0.73  thf('78', plain, ((v1_funct_1 @ sk_B_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('79', plain,
% 0.50/0.73      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.50/0.73        | ~ (v1_partfun1 @ sk_B_1 @ (k1_relat_1 @ sk_B_1)))),
% 0.50/0.73      inference('demod', [status(thm)], ['77', '78'])).
% 0.50/0.73  thf('80', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.50/0.73      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 0.50/0.73  thf('81', plain, (~ (v1_partfun1 @ sk_B_1 @ (k1_relat_1 @ sk_B_1))),
% 0.50/0.73      inference('clc', [status(thm)], ['79', '80'])).
% 0.50/0.73  thf('82', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 0.50/0.73      inference('sup-', [status(thm)], ['74', '81'])).
% 0.50/0.73  thf('83', plain, ((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.50/0.73      inference('demod', [status(thm)], ['27', '82'])).
% 0.50/0.73  thf('84', plain, ($false), inference('demod', [status(thm)], ['24', '83'])).
% 0.50/0.73  
% 0.50/0.73  % SZS output end Refutation
% 0.50/0.73  
% 0.50/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
