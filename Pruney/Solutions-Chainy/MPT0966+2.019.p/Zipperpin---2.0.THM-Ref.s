%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c8iQeYz4k8

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:08 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  216 (1142 expanded)
%              Number of leaves         :   42 ( 344 expanded)
%              Depth                    :   25
%              Number of atoms          : 1424 (14309 expanded)
%              Number of equality atoms :  113 ( 921 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','20'])).

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

thf(zf_stmt_0,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('22',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','32'])).

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

thf(zf_stmt_5,negated_conjecture,(
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

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['49','54'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('56',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('64',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['39','62','63'])).

thf('65',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['36','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('71',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('75',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('78',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['76','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('81',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('82',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('84',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('89',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('96',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('99',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['24','30'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('106',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('110',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('112',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('113',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('118',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('119',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('120',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('121',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','123'])).

thf('125',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('126',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('127',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('128',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('130',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['95'])).

thf('131',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','115','128','129','130'])).

thf('132',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['100','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['91','132'])).

thf('134',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('135',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['133','136'])).

thf('138',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['75','137'])).

thf('139',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['72','138'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('140',plain,(
    ! [X19: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('141',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['65','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','59'])).

thf('144',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('145',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('147',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('149',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','59'])).

thf('150',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('151',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','59'])).

thf('153',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('154',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['72','138'])).

thf('156',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('161',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['39','62','63'])).

thf('162',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['159','162'])).

thf('164',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['151','163'])).

thf('165',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['148','164'])).

thf('166',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('167',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('168',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['148','164'])).

thf('169',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('170',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['147','165','166','167','168','169'])).

thf('171',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('172',plain,(
    $false ),
    inference(demod,[status(thm)],['142','170','171'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c8iQeYz4k8
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.91/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.08  % Solved by: fo/fo7.sh
% 0.91/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.08  % done 1278 iterations in 0.630s
% 0.91/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.08  % SZS output start Refutation
% 0.91/1.08  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.91/1.08  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.91/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.91/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.08  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.91/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.08  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.91/1.08  thf(sk_D_type, type, sk_D: $i).
% 0.91/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.08  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.91/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.08  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.08  thf(l13_xboole_0, axiom,
% 0.91/1.08    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.08  thf('0', plain,
% 0.91/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.08  thf('1', plain,
% 0.91/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.08  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.91/1.08  thf('2', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.91/1.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.91/1.08  thf(t3_subset, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.08  thf('3', plain,
% 0.91/1.08      (![X9 : $i, X11 : $i]:
% 0.91/1.08         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.08  thf('4', plain,
% 0.91/1.08      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.08  thf(redefinition_k1_relset_1, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.08       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.91/1.08  thf('5', plain,
% 0.91/1.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.91/1.08         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.91/1.08          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.91/1.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.08  thf('6', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.08  thf('7', plain,
% 0.91/1.08      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.08  thf(cc2_relset_1, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.08       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.91/1.08  thf('8', plain,
% 0.91/1.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.08         ((v4_relat_1 @ X23 @ X24)
% 0.91/1.08          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.91/1.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.08  thf('9', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.91/1.08      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.08  thf(d18_relat_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ B ) =>
% 0.91/1.08       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.08  thf('10', plain,
% 0.91/1.08      (![X17 : $i, X18 : $i]:
% 0.91/1.08         (~ (v4_relat_1 @ X17 @ X18)
% 0.91/1.08          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.91/1.08          | ~ (v1_relat_1 @ X17))),
% 0.91/1.08      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.91/1.08  thf('11', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ k1_xboole_0)
% 0.91/1.08          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.08  thf(t113_zfmisc_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.08       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.91/1.08  thf('12', plain,
% 0.91/1.08      (![X7 : $i, X8 : $i]:
% 0.91/1.08         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.91/1.08      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.91/1.08  thf('13', plain,
% 0.91/1.08      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['12'])).
% 0.91/1.08  thf(fc6_relat_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.91/1.08  thf('14', plain,
% 0.91/1.08      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.91/1.08  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.91/1.08      inference('sup+', [status(thm)], ['13', '14'])).
% 0.91/1.08  thf('16', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['11', '15'])).
% 0.91/1.08  thf('17', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.91/1.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.91/1.08  thf(d10_xboole_0, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.08  thf('18', plain,
% 0.91/1.08      (![X2 : $i, X4 : $i]:
% 0.91/1.08         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.91/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.08  thf('19', plain,
% 0.91/1.08      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['17', '18'])).
% 0.91/1.08  thf('20', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['16', '19'])).
% 0.91/1.08  thf('21', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.08      inference('demod', [status(thm)], ['6', '20'])).
% 0.91/1.08  thf(d1_funct_2, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.08       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.08           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.91/1.08             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.91/1.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.08           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.91/1.08             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.91/1.08  thf(zf_stmt_0, axiom,
% 0.91/1.08    (![C:$i,B:$i,A:$i]:
% 0.91/1.08     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.91/1.08       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.91/1.08  thf('22', plain,
% 0.91/1.08      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.91/1.08         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 0.91/1.08          | (v1_funct_2 @ X40 @ X38 @ X39)
% 0.91/1.08          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('23', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (((X1) != (k1_xboole_0))
% 0.91/1.08          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.91/1.08          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['21', '22'])).
% 0.91/1.08  thf('24', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.91/1.08          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['23'])).
% 0.91/1.08  thf(zf_stmt_1, axiom,
% 0.91/1.08    (![B:$i,A:$i]:
% 0.91/1.08     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.08       ( zip_tseitin_0 @ B @ A ) ))).
% 0.91/1.08  thf('25', plain,
% 0.91/1.08      (![X36 : $i, X37 : $i]:
% 0.91/1.08         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.08  thf('26', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 0.91/1.08      inference('simplify', [status(thm)], ['25'])).
% 0.91/1.08  thf('27', plain,
% 0.91/1.08      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.08  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.91/1.08  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.91/1.08  thf(zf_stmt_4, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.08       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.91/1.08         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.08           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.91/1.08             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.91/1.08  thf('28', plain,
% 0.91/1.08      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.91/1.08         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.91/1.08          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.91/1.08          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.91/1.08  thf('29', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.91/1.08      inference('sup-', [status(thm)], ['27', '28'])).
% 0.91/1.08  thf('30', plain,
% 0.91/1.08      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.91/1.08      inference('sup-', [status(thm)], ['26', '29'])).
% 0.91/1.08  thf('31', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['24', '30'])).
% 0.91/1.08  thf('32', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('sup+', [status(thm)], ['1', '31'])).
% 0.91/1.08  thf('33', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         ((v1_funct_2 @ X2 @ X0 @ X1)
% 0.91/1.08          | ~ (v1_xboole_0 @ X0)
% 0.91/1.08          | ~ (v1_xboole_0 @ X2))),
% 0.91/1.08      inference('sup+', [status(thm)], ['0', '32'])).
% 0.91/1.08  thf(t8_funct_2, conjecture,
% 0.91/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.08     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.08       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.91/1.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.91/1.08           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.91/1.08             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.91/1.08  thf(zf_stmt_5, negated_conjecture,
% 0.91/1.08    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.08        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.08            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.08          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 0.91/1.08            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.91/1.08              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.91/1.08                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.91/1.08    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 0.91/1.08  thf('34', plain,
% 0.91/1.08      ((~ (v1_funct_1 @ sk_D)
% 0.91/1.08        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.91/1.08        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('35', plain,
% 0.91/1.08      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.91/1.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.91/1.08      inference('split', [status(esa)], ['34'])).
% 0.91/1.08  thf('36', plain,
% 0.91/1.08      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 0.91/1.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['33', '35'])).
% 0.91/1.08  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('38', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.91/1.08      inference('split', [status(esa)], ['34'])).
% 0.91/1.08  thf('39', plain, (((v1_funct_1 @ sk_D))),
% 0.91/1.08      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.08  thf('40', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('41', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf(redefinition_k2_relset_1, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.08       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.91/1.08  thf('42', plain,
% 0.91/1.08      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.91/1.08         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.91/1.08          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.91/1.08      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.08  thf('43', plain,
% 0.91/1.08      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.91/1.08      inference('sup-', [status(thm)], ['41', '42'])).
% 0.91/1.08  thf('44', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.91/1.08      inference('demod', [status(thm)], ['40', '43'])).
% 0.91/1.08  thf('45', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('46', plain,
% 0.91/1.08      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.08         ((v4_relat_1 @ X23 @ X24)
% 0.91/1.08          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.91/1.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.08  thf('47', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.91/1.08      inference('sup-', [status(thm)], ['45', '46'])).
% 0.91/1.08  thf('48', plain,
% 0.91/1.08      (![X17 : $i, X18 : $i]:
% 0.91/1.08         (~ (v4_relat_1 @ X17 @ X18)
% 0.91/1.08          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.91/1.08          | ~ (v1_relat_1 @ X17))),
% 0.91/1.08      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.91/1.08  thf('49', plain,
% 0.91/1.08      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.91/1.08      inference('sup-', [status(thm)], ['47', '48'])).
% 0.91/1.08  thf('50', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf(cc2_relat_1, axiom,
% 0.91/1.08    (![A:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ A ) =>
% 0.91/1.08       ( ![B:$i]:
% 0.91/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.91/1.08  thf('51', plain,
% 0.91/1.08      (![X15 : $i, X16 : $i]:
% 0.91/1.08         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.91/1.08          | (v1_relat_1 @ X15)
% 0.91/1.08          | ~ (v1_relat_1 @ X16))),
% 0.91/1.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.91/1.08  thf('52', plain,
% 0.91/1.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 0.91/1.08      inference('sup-', [status(thm)], ['50', '51'])).
% 0.91/1.08  thf('53', plain,
% 0.91/1.08      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.91/1.08  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.08      inference('demod', [status(thm)], ['52', '53'])).
% 0.91/1.08  thf('55', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.91/1.08      inference('demod', [status(thm)], ['49', '54'])).
% 0.91/1.08  thf(t11_relset_1, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( v1_relat_1 @ C ) =>
% 0.91/1.08       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.91/1.08           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.91/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.91/1.08  thf('56', plain,
% 0.91/1.08      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.91/1.08         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.91/1.08          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 0.91/1.08          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.91/1.08          | ~ (v1_relat_1 @ X32))),
% 0.91/1.08      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.91/1.08  thf('57', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (v1_relat_1 @ sk_D)
% 0.91/1.08          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.91/1.08          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['55', '56'])).
% 0.91/1.08  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.08      inference('demod', [status(thm)], ['52', '53'])).
% 0.91/1.08  thf('59', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.91/1.08          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.91/1.08      inference('demod', [status(thm)], ['57', '58'])).
% 0.91/1.08  thf('60', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['44', '59'])).
% 0.91/1.08  thf('61', plain,
% 0.91/1.08      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.91/1.08         <= (~
% 0.91/1.08             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.91/1.08      inference('split', [status(esa)], ['34'])).
% 0.91/1.08  thf('62', plain,
% 0.91/1.08      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['60', '61'])).
% 0.91/1.08  thf('63', plain,
% 0.91/1.08      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.91/1.08       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.91/1.08       ~ ((v1_funct_1 @ sk_D))),
% 0.91/1.08      inference('split', [status(esa)], ['34'])).
% 0.91/1.08  thf('64', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.91/1.08      inference('sat_resolution*', [status(thm)], ['39', '62', '63'])).
% 0.91/1.08  thf('65', plain, ((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.91/1.08      inference('simpl_trail', [status(thm)], ['36', '64'])).
% 0.91/1.08  thf('66', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('67', plain,
% 0.91/1.08      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.91/1.08         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.91/1.08          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 0.91/1.08          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('68', plain,
% 0.91/1.08      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.08        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['66', '67'])).
% 0.91/1.08  thf('69', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('70', plain,
% 0.91/1.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.91/1.08         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.91/1.08          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.91/1.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.08  thf('71', plain,
% 0.91/1.08      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.91/1.08      inference('sup-', [status(thm)], ['69', '70'])).
% 0.91/1.08  thf('72', plain,
% 0.91/1.08      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.08        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.08      inference('demod', [status(thm)], ['68', '71'])).
% 0.91/1.08  thf('73', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('74', plain,
% 0.91/1.08      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.91/1.08         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.91/1.08          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.91/1.08          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.91/1.08  thf('75', plain,
% 0.91/1.08      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.08        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.91/1.08      inference('sup-', [status(thm)], ['73', '74'])).
% 0.91/1.08  thf('76', plain,
% 0.91/1.08      (![X36 : $i, X37 : $i]:
% 0.91/1.08         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.08  thf('77', plain,
% 0.91/1.08      (![X7 : $i, X8 : $i]:
% 0.91/1.08         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.91/1.08      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.91/1.08  thf('78', plain,
% 0.91/1.08      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['77'])).
% 0.91/1.08  thf('79', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.91/1.08      inference('sup+', [status(thm)], ['76', '78'])).
% 0.91/1.08  thf('80', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('81', plain,
% 0.91/1.08      (![X9 : $i, X10 : $i]:
% 0.91/1.08         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.08  thf('82', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.91/1.08      inference('sup-', [status(thm)], ['80', '81'])).
% 0.91/1.08  thf('83', plain,
% 0.91/1.08      (![X2 : $i, X4 : $i]:
% 0.91/1.08         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.91/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.08  thf('84', plain,
% 0.91/1.08      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_D)
% 0.91/1.08        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['82', '83'])).
% 0.91/1.08  thf('85', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 0.91/1.08          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 0.91/1.08          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['79', '84'])).
% 0.91/1.08  thf('86', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.91/1.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.91/1.08  thf('87', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 0.91/1.08          | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_D)))),
% 0.91/1.08      inference('demod', [status(thm)], ['85', '86'])).
% 0.91/1.08  thf('88', plain,
% 0.91/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.08  thf('89', plain,
% 0.91/1.08      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['77'])).
% 0.91/1.08  thf('90', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('sup+', [status(thm)], ['88', '89'])).
% 0.91/1.08  thf('91', plain,
% 0.91/1.08      (![X0 : $i]:
% 0.91/1.08         (((sk_D) = (k1_xboole_0))
% 0.91/1.08          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 0.91/1.08          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.91/1.08      inference('sup+', [status(thm)], ['87', '90'])).
% 0.91/1.08  thf('92', plain,
% 0.91/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.08  thf('93', plain,
% 0.91/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.08  thf('94', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.91/1.08      inference('sup+', [status(thm)], ['92', '93'])).
% 0.91/1.08  thf('95', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('96', plain,
% 0.91/1.08      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.08      inference('split', [status(esa)], ['95'])).
% 0.91/1.08  thf('97', plain,
% 0.91/1.08      ((![X0 : $i]:
% 0.91/1.08          (((X0) != (k1_xboole_0))
% 0.91/1.08           | ~ (v1_xboole_0 @ X0)
% 0.91/1.08           | ~ (v1_xboole_0 @ sk_B_1)))
% 0.91/1.08         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['94', '96'])).
% 0.91/1.08  thf('98', plain,
% 0.91/1.08      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.91/1.08         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.08      inference('simplify', [status(thm)], ['97'])).
% 0.91/1.08  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.91/1.08  thf('99', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.08  thf('100', plain,
% 0.91/1.08      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.08      inference('simplify_reflect+', [status(thm)], ['98', '99'])).
% 0.91/1.08  thf('101', plain,
% 0.91/1.08      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.91/1.08      inference('demod', [status(thm)], ['24', '30'])).
% 0.91/1.08  thf('102', plain,
% 0.91/1.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('split', [status(esa)], ['95'])).
% 0.91/1.08  thf('103', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('104', plain,
% 0.91/1.08      (((m1_subset_1 @ sk_D @ 
% 0.91/1.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.91/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('sup+', [status(thm)], ['102', '103'])).
% 0.91/1.08  thf('105', plain,
% 0.91/1.08      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['12'])).
% 0.91/1.08  thf('106', plain,
% 0.91/1.08      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.91/1.08         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('demod', [status(thm)], ['104', '105'])).
% 0.91/1.08  thf('107', plain,
% 0.91/1.08      (![X9 : $i, X10 : $i]:
% 0.91/1.08         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.08  thf('108', plain,
% 0.91/1.08      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['106', '107'])).
% 0.91/1.08  thf('109', plain,
% 0.91/1.08      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['17', '18'])).
% 0.91/1.08  thf('110', plain,
% 0.91/1.08      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['108', '109'])).
% 0.91/1.08  thf('111', plain,
% 0.91/1.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('split', [status(esa)], ['95'])).
% 0.91/1.08  thf('112', plain,
% 0.91/1.08      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.91/1.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.91/1.08      inference('split', [status(esa)], ['34'])).
% 0.91/1.08  thf('113', plain,
% 0.91/1.08      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.91/1.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['111', '112'])).
% 0.91/1.08  thf('114', plain,
% 0.91/1.08      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 0.91/1.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['110', '113'])).
% 0.91/1.08  thf('115', plain,
% 0.91/1.08      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['101', '114'])).
% 0.91/1.08  thf('116', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.08  thf('117', plain,
% 0.91/1.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.08      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.08  thf('118', plain,
% 0.91/1.08      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['12'])).
% 0.91/1.08  thf('119', plain,
% 0.91/1.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('split', [status(esa)], ['95'])).
% 0.91/1.08  thf('120', plain,
% 0.91/1.08      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.91/1.08         <= (~
% 0.91/1.08             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.91/1.08      inference('split', [status(esa)], ['34'])).
% 0.91/1.08  thf('121', plain,
% 0.91/1.08      ((~ (m1_subset_1 @ sk_D @ 
% 0.91/1.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.91/1.08         <= (~
% 0.91/1.08             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.91/1.08             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['119', '120'])).
% 0.91/1.08  thf('122', plain,
% 0.91/1.08      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.91/1.08         <= (~
% 0.91/1.08             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.91/1.08             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['118', '121'])).
% 0.91/1.08  thf('123', plain,
% 0.91/1.08      ((![X0 : $i]:
% 0.91/1.08          (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.91/1.08         <= (~
% 0.91/1.08             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.91/1.08             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['117', '122'])).
% 0.91/1.08  thf('124', plain,
% 0.91/1.08      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.91/1.08         <= (~
% 0.91/1.08             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.91/1.08             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('sup-', [status(thm)], ['116', '123'])).
% 0.91/1.08  thf('125', plain,
% 0.91/1.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.08      inference('split', [status(esa)], ['95'])).
% 0.91/1.08  thf('126', plain,
% 0.91/1.08      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['12'])).
% 0.91/1.08  thf('127', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.08  thf('128', plain,
% 0.91/1.08      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.91/1.08       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.91/1.08      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 0.91/1.08  thf('129', plain,
% 0.91/1.08      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.91/1.08       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.91/1.08      inference('split', [status(esa)], ['34'])).
% 0.91/1.08  thf('130', plain,
% 0.91/1.08      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.91/1.08      inference('split', [status(esa)], ['95'])).
% 0.91/1.08  thf('131', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.08      inference('sat_resolution*', [status(thm)],
% 0.91/1.08                ['39', '115', '128', '129', '130'])).
% 0.91/1.08  thf('132', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.91/1.08      inference('simpl_trail', [status(thm)], ['100', '131'])).
% 0.91/1.08  thf('133', plain,
% 0.91/1.08      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 0.91/1.08      inference('clc', [status(thm)], ['91', '132'])).
% 0.91/1.08  thf('134', plain,
% 0.91/1.08      (![X36 : $i, X37 : $i]:
% 0.91/1.08         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.08  thf('135', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.08  thf('136', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.91/1.08      inference('sup+', [status(thm)], ['134', '135'])).
% 0.91/1.08  thf('137', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.91/1.08      inference('clc', [status(thm)], ['133', '136'])).
% 0.91/1.08  thf('138', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.91/1.08      inference('demod', [status(thm)], ['75', '137'])).
% 0.91/1.08  thf('139', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.91/1.08      inference('demod', [status(thm)], ['72', '138'])).
% 0.91/1.08  thf(fc10_relat_1, axiom,
% 0.91/1.08    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.91/1.08  thf('140', plain,
% 0.91/1.08      (![X19 : $i]:
% 0.91/1.08         ((v1_xboole_0 @ (k1_relat_1 @ X19)) | ~ (v1_xboole_0 @ X19))),
% 0.91/1.08      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.91/1.08  thf('141', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 0.91/1.08      inference('sup+', [status(thm)], ['139', '140'])).
% 0.91/1.08  thf('142', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.91/1.08      inference('clc', [status(thm)], ['65', '141'])).
% 0.91/1.08  thf('143', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['44', '59'])).
% 0.91/1.08  thf('144', plain,
% 0.91/1.08      (![X9 : $i, X10 : $i]:
% 0.91/1.08         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.08  thf('145', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.91/1.08      inference('sup-', [status(thm)], ['143', '144'])).
% 0.91/1.08  thf('146', plain,
% 0.91/1.08      (![X2 : $i, X4 : $i]:
% 0.91/1.08         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.91/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.08  thf('147', plain,
% 0.91/1.08      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 0.91/1.08        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['145', '146'])).
% 0.91/1.08  thf('148', plain,
% 0.91/1.08      (![X36 : $i, X37 : $i]:
% 0.91/1.08         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.08  thf('149', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['44', '59'])).
% 0.91/1.08  thf('150', plain,
% 0.91/1.08      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.91/1.08         (~ (zip_tseitin_0 @ X41 @ X42)
% 0.91/1.08          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 0.91/1.08          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.91/1.08  thf('151', plain,
% 0.91/1.08      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.91/1.08      inference('sup-', [status(thm)], ['149', '150'])).
% 0.91/1.08  thf('152', plain,
% 0.91/1.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.91/1.08      inference('sup-', [status(thm)], ['44', '59'])).
% 0.91/1.08  thf('153', plain,
% 0.91/1.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.91/1.08         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.91/1.08          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.91/1.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.08  thf('154', plain,
% 0.91/1.08      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.91/1.08      inference('sup-', [status(thm)], ['152', '153'])).
% 0.91/1.08  thf('155', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.91/1.08      inference('demod', [status(thm)], ['72', '138'])).
% 0.91/1.08  thf('156', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 0.91/1.08      inference('demod', [status(thm)], ['154', '155'])).
% 0.91/1.08  thf('157', plain,
% 0.91/1.08      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.91/1.08         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 0.91/1.08          | (v1_funct_2 @ X40 @ X38 @ X39)
% 0.91/1.08          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf('158', plain,
% 0.91/1.08      ((((sk_A) != (sk_A))
% 0.91/1.08        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.91/1.08        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.91/1.08      inference('sup-', [status(thm)], ['156', '157'])).
% 0.91/1.08  thf('159', plain,
% 0.91/1.08      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.91/1.08        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.91/1.08      inference('simplify', [status(thm)], ['158'])).
% 0.91/1.08  thf('160', plain,
% 0.91/1.08      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.91/1.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.91/1.08      inference('split', [status(esa)], ['34'])).
% 0.91/1.08  thf('161', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.91/1.08      inference('sat_resolution*', [status(thm)], ['39', '62', '63'])).
% 0.91/1.08  thf('162', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.91/1.08      inference('simpl_trail', [status(thm)], ['160', '161'])).
% 0.91/1.08  thf('163', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.91/1.08      inference('clc', [status(thm)], ['159', '162'])).
% 0.91/1.08  thf('164', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 0.91/1.08      inference('clc', [status(thm)], ['151', '163'])).
% 0.91/1.08  thf('165', plain, (((sk_C) = (k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['148', '164'])).
% 0.91/1.08  thf('166', plain,
% 0.91/1.08      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['77'])).
% 0.91/1.08  thf('167', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.91/1.08      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.91/1.08  thf('168', plain, (((sk_C) = (k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['148', '164'])).
% 0.91/1.08  thf('169', plain,
% 0.91/1.08      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.08      inference('simplify', [status(thm)], ['77'])).
% 0.91/1.08  thf('170', plain, (((k1_xboole_0) = (sk_D))),
% 0.91/1.08      inference('demod', [status(thm)],
% 0.91/1.08                ['147', '165', '166', '167', '168', '169'])).
% 0.91/1.08  thf('171', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.08  thf('172', plain, ($false),
% 0.91/1.08      inference('demod', [status(thm)], ['142', '170', '171'])).
% 0.91/1.08  
% 0.91/1.08  % SZS output end Refutation
% 0.91/1.08  
% 0.91/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
