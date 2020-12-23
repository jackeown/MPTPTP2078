%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QVZaQ4ISmh

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:14 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 342 expanded)
%              Number of leaves         :   44 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  784 (3823 expanded)
%              Number of equality atoms :   48 ( 216 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
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

thf('6',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('13',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( v5_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ X22 ) )
      | ( r2_hidden @ X21 @ X23 )
      | ~ ( v5_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v5_relat_1 @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference(condensation,[status(thm)],['41'])).

thf('43',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['14','42'])).

thf('44',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['11','43'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X20: $i] :
      ( ( ( k9_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('46',plain,
    ( ( ( k9_relat_1 @ sk_D_1 @ sk_B )
      = ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('48',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_B )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X19 @ X17 @ X18 ) @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ X0 ) @ X0 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ X0 ) @ X0 ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['4','52'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('54',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ X25 )
      | ( X26
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('57',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('60',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_B )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( sk_D @ X19 @ X17 @ X18 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('64',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['11','43'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['59','65'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('67',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('68',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X47: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QVZaQ4ISmh
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.66  % Solved by: fo/fo7.sh
% 0.48/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.66  % done 307 iterations in 0.207s
% 0.48/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.66  % SZS output start Refutation
% 0.48/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.48/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.48/0.66  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.48/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.48/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.48/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.48/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.48/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.48/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.48/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.48/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.48/0.66  thf(t190_funct_2, conjecture,
% 0.48/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.48/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.48/0.66       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.48/0.66            ( ![E:$i]:
% 0.48/0.66              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.66        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.48/0.66            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.48/0.66          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.48/0.66               ( ![E:$i]:
% 0.48/0.66                 ( ( m1_subset_1 @ E @ B ) =>
% 0.48/0.66                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.48/0.66    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.48/0.66  thf('0', plain, ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('1', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.48/0.66  thf('2', plain,
% 0.48/0.66      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.48/0.66         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.48/0.66          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.48/0.66  thf('3', plain,
% 0.48/0.66      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.66  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.66  thf('5', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(d1_funct_2, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.48/0.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.48/0.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.48/0.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_1, axiom,
% 0.48/0.66    (![C:$i,B:$i,A:$i]:
% 0.48/0.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.48/0.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.48/0.66  thf('6', plain,
% 0.48/0.66      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.48/0.66         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.48/0.66          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.48/0.66          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.48/0.66  thf('7', plain,
% 0.48/0.66      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.48/0.66        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.66  thf('8', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(redefinition_k1_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.48/0.66  thf('9', plain,
% 0.48/0.66      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.48/0.66         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.48/0.66          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.48/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.48/0.66  thf('10', plain,
% 0.48/0.66      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.66  thf('11', plain,
% 0.48/0.66      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.48/0.66        | ((sk_B) = (k1_relat_1 @ sk_D_1)))),
% 0.48/0.66      inference('demod', [status(thm)], ['7', '10'])).
% 0.48/0.66  thf('12', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.48/0.66  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.48/0.66  thf(zf_stmt_4, axiom,
% 0.48/0.66    (![B:$i,A:$i]:
% 0.48/0.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.66       ( zip_tseitin_0 @ B @ A ) ))).
% 0.48/0.66  thf(zf_stmt_5, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.48/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.48/0.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.48/0.66  thf('13', plain,
% 0.48/0.66      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.48/0.66         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.48/0.66          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.48/0.66          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.48/0.66  thf('14', plain,
% 0.48/0.66      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.48/0.66        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.48/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.48/0.66  thf('15', plain,
% 0.48/0.66      (![X39 : $i, X40 : $i]:
% 0.48/0.66         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.48/0.66  thf(t113_zfmisc_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.48/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.48/0.66  thf('16', plain,
% 0.48/0.66      (![X4 : $i, X5 : $i]:
% 0.48/0.66         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.48/0.66  thf('17', plain,
% 0.48/0.66      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.66      inference('simplify', [status(thm)], ['16'])).
% 0.48/0.66  thf('18', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.48/0.66      inference('sup+', [status(thm)], ['15', '17'])).
% 0.48/0.66  thf('19', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('20', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.48/0.66          | (zip_tseitin_0 @ sk_C @ X0))),
% 0.48/0.66      inference('sup+', [status(thm)], ['18', '19'])).
% 0.48/0.66  thf('21', plain,
% 0.48/0.66      (![X4 : $i, X5 : $i]:
% 0.48/0.66         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.48/0.66  thf('22', plain,
% 0.48/0.66      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.48/0.66      inference('simplify', [status(thm)], ['21'])).
% 0.48/0.66  thf(cc2_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.48/0.66  thf('23', plain,
% 0.48/0.66      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.48/0.66         ((v5_relat_1 @ X30 @ X32)
% 0.48/0.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.48/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.48/0.66  thf('24', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.48/0.66          | (v5_relat_1 @ X1 @ X0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.48/0.66  thf('25', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((zip_tseitin_0 @ sk_C @ X1) | (v5_relat_1 @ sk_D_1 @ X0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['20', '24'])).
% 0.48/0.66  thf('26', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.66  thf(t202_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.48/0.66       ( ![C:$i]:
% 0.48/0.66         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.48/0.66  thf('27', plain,
% 0.48/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X21 @ (k2_relat_1 @ X22))
% 0.48/0.66          | (r2_hidden @ X21 @ X23)
% 0.48/0.66          | ~ (v5_relat_1 @ X22 @ X23)
% 0.48/0.66          | ~ (v1_relat_1 @ X22))),
% 0.48/0.66      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.48/0.66  thf('28', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (v1_relat_1 @ sk_D_1)
% 0.48/0.66          | ~ (v5_relat_1 @ sk_D_1 @ X0)
% 0.48/0.66          | (r2_hidden @ sk_A @ X0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.48/0.66  thf('29', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(cc1_relset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.66       ( v1_relat_1 @ C ) ))).
% 0.48/0.66  thf('30', plain,
% 0.48/0.66      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.48/0.66         ((v1_relat_1 @ X27)
% 0.48/0.66          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.48/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.48/0.66  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.66  thf('32', plain,
% 0.48/0.66      (![X0 : $i]: (~ (v5_relat_1 @ sk_D_1 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.48/0.66      inference('demod', [status(thm)], ['28', '31'])).
% 0.48/0.66  thf('33', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((zip_tseitin_0 @ sk_C @ X1) | (r2_hidden @ sk_A @ X0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['25', '32'])).
% 0.48/0.66  thf('34', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.66         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.48/0.66      inference('sup+', [status(thm)], ['15', '17'])).
% 0.48/0.66  thf('35', plain,
% 0.48/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(t5_subset, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.48/0.66          ( v1_xboole_0 @ C ) ) ))).
% 0.48/0.66  thf('36', plain,
% 0.48/0.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X11 @ X12)
% 0.48/0.66          | ~ (v1_xboole_0 @ X13)
% 0.48/0.66          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t5_subset])).
% 0.48/0.66  thf('37', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.48/0.66          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.48/0.66  thf('38', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.48/0.66          | (zip_tseitin_0 @ sk_C @ X1)
% 0.48/0.66          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['34', '37'])).
% 0.48/0.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.48/0.66  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.66  thf('40', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((zip_tseitin_0 @ sk_C @ X1) | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.48/0.66  thf('41', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((zip_tseitin_0 @ sk_C @ X1) | (zip_tseitin_0 @ sk_C @ X0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['33', '40'])).
% 0.48/0.66  thf('42', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.48/0.66      inference('condensation', [status(thm)], ['41'])).
% 0.48/0.66  thf('43', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 0.48/0.66      inference('demod', [status(thm)], ['14', '42'])).
% 0.48/0.66  thf('44', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['11', '43'])).
% 0.48/0.66  thf(t146_relat_1, axiom,
% 0.48/0.66    (![A:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ A ) =>
% 0.48/0.66       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.48/0.66  thf('45', plain,
% 0.48/0.66      (![X20 : $i]:
% 0.48/0.66         (((k9_relat_1 @ X20 @ (k1_relat_1 @ X20)) = (k2_relat_1 @ X20))
% 0.48/0.66          | ~ (v1_relat_1 @ X20))),
% 0.48/0.66      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.48/0.66  thf('46', plain,
% 0.48/0.66      ((((k9_relat_1 @ sk_D_1 @ sk_B) = (k2_relat_1 @ sk_D_1))
% 0.48/0.66        | ~ (v1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('sup+', [status(thm)], ['44', '45'])).
% 0.48/0.66  thf('47', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.66  thf('48', plain, (((k9_relat_1 @ sk_D_1 @ sk_B) = (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['46', '47'])).
% 0.48/0.66  thf(t143_relat_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( v1_relat_1 @ C ) =>
% 0.48/0.66       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.48/0.66         ( ?[D:$i]:
% 0.48/0.66           ( ( r2_hidden @ D @ B ) & 
% 0.48/0.66             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.48/0.66             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.48/0.66  thf('49', plain,
% 0.48/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X18 @ (k9_relat_1 @ X19 @ X17))
% 0.48/0.66          | (r2_hidden @ (k4_tarski @ (sk_D @ X19 @ X17 @ X18) @ X18) @ X19)
% 0.48/0.66          | ~ (v1_relat_1 @ X19))),
% 0.48/0.66      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.48/0.66  thf('50', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.48/0.66          | ~ (v1_relat_1 @ sk_D_1)
% 0.48/0.66          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ X0) @ X0) @ 
% 0.48/0.66             sk_D_1))),
% 0.48/0.66      inference('sup-', [status(thm)], ['48', '49'])).
% 0.48/0.66  thf('51', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.66  thf('52', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.48/0.66          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ X0) @ X0) @ 
% 0.48/0.66             sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['50', '51'])).
% 0.48/0.66  thf('53', plain,
% 0.48/0.66      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_A) @ sk_D_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['4', '52'])).
% 0.48/0.66  thf(t8_funct_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.48/0.66       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.48/0.66         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.48/0.66           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.48/0.66  thf('54', plain,
% 0.48/0.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.48/0.66         (~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ X25)
% 0.48/0.66          | ((X26) = (k1_funct_1 @ X25 @ X24))
% 0.48/0.66          | ~ (v1_funct_1 @ X25)
% 0.48/0.66          | ~ (v1_relat_1 @ X25))),
% 0.48/0.66      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.48/0.66  thf('55', plain,
% 0.48/0.66      ((~ (v1_relat_1 @ sk_D_1)
% 0.48/0.66        | ~ (v1_funct_1 @ sk_D_1)
% 0.48/0.66        | ((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A))))),
% 0.48/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.66  thf('56', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.66  thf('57', plain, ((v1_funct_1 @ sk_D_1)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('58', plain,
% 0.48/0.66      (((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)))),
% 0.48/0.66      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.48/0.66  thf('59', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['0', '3'])).
% 0.48/0.66  thf('60', plain, (((k9_relat_1 @ sk_D_1 @ sk_B) = (k2_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['46', '47'])).
% 0.48/0.66  thf('61', plain,
% 0.48/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X18 @ (k9_relat_1 @ X19 @ X17))
% 0.48/0.66          | (r2_hidden @ (sk_D @ X19 @ X17 @ X18) @ (k1_relat_1 @ X19))
% 0.48/0.66          | ~ (v1_relat_1 @ X19))),
% 0.48/0.66      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.48/0.66  thf('62', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.48/0.66          | ~ (v1_relat_1 @ sk_D_1)
% 0.48/0.66          | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_D_1)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['60', '61'])).
% 0.48/0.66  thf('63', plain, ((v1_relat_1 @ sk_D_1)),
% 0.48/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.66  thf('64', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.48/0.66      inference('demod', [status(thm)], ['11', '43'])).
% 0.48/0.66  thf('65', plain,
% 0.48/0.66      (![X0 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.48/0.66          | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ X0) @ sk_B))),
% 0.48/0.66      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.48/0.66  thf('66', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_B)),
% 0.48/0.66      inference('sup-', [status(thm)], ['59', '65'])).
% 0.48/0.66  thf(t1_subset, axiom,
% 0.48/0.66    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.48/0.66  thf('67', plain,
% 0.48/0.66      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.48/0.66      inference('cnf', [status(esa)], [t1_subset])).
% 0.48/0.66  thf('68', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A) @ sk_B)),
% 0.48/0.66      inference('sup-', [status(thm)], ['66', '67'])).
% 0.48/0.66  thf('69', plain,
% 0.48/0.66      (![X47 : $i]:
% 0.48/0.66         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X47))
% 0.48/0.66          | ~ (m1_subset_1 @ X47 @ sk_B))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('70', plain,
% 0.48/0.66      (((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_A)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['68', '69'])).
% 0.48/0.66  thf('71', plain, ($false),
% 0.48/0.66      inference('simplify_reflect-', [status(thm)], ['58', '70'])).
% 0.48/0.66  
% 0.48/0.66  % SZS output end Refutation
% 0.48/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
