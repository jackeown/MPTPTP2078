%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fM3JBXi886

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:52 EST 2020

% Result     : Theorem 4.41s
% Output     : Refutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :  252 (1251 expanded)
%              Number of leaves         :   51 ( 388 expanded)
%              Depth                    :   20
%              Number of atoms          : 1984 (20466 expanded)
%              Number of equality atoms :  121 ( 412 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X42 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X41: $i] :
      ( zip_tseitin_0 @ X41 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('6',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X40 ) ) )
      | ( v1_partfun1 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_partfun1 @ X35 @ X36 )
      | ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(t178_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ~ ( v1_xboole_0 @ D )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ A @ D )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
         => ( ( ( r1_tarski @ B @ A )
              & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
           => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ~ ( v1_xboole_0 @ D )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ A @ D )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
           => ( ( ( r1_tarski @ B @ A )
                & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
             => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
                & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
                & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_funct_2])).

thf('16',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X50 @ X51 @ X49 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('22',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ( ( k2_partfun1 @ X54 @ X55 @ X53 @ X56 )
        = ( k7_relat_1 @ X53 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','34'])).

thf('36',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( X1
        = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','34'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('65',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('71',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_A @ sk_D @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['65','74','77'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('79',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['30','31'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['62','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','53'])).

thf('85',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','50'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['61','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['58'])).

thf('93',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('95',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('96',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['94','97'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('99',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('100',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( v5_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('104',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X50 @ X51 @ X49 @ X52 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('107',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
      | ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('113',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['30','31'])).

thf('115',plain,(
    v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['102','113','114'])).

thf('116',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('119',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('121',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X34 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('125',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['30','31'])).

thf('126',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('128',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('129',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['58'])).

thf('132',plain,(
    ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['93','130','131'])).

thf('133',plain,(
    ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['90','132'])).

thf('134',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('135',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_E @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('142',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['65','74','77'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('143',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k9_relat_1 @ X20 @ X19 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_E @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['30','31'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_E @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_E @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['140','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','53'])).

thf('153',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X46 != k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ( X48 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('154',plain,(
    ! [X47: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X47 @ k1_xboole_0 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('156',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('158',plain,(
    ! [X47: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X47 @ k1_xboole_0 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['154','156','157'])).

thf('159',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','51'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['152','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['151','164'])).

thf('166',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference(condensation,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('168',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('169',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X47 )
      | ( zip_tseitin_1 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('170',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['167','170'])).

thf('172',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('173',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('174',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['62','82'])).

thf('176',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43
       != ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ~ ( zip_tseitin_1 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('178',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['58'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('182',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['93','130','131'])).

thf('184',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['179','184'])).

thf('186',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['171','185'])).

thf('187',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['166','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['30','31'])).

thf('189',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( ( k7_relat_1 @ sk_E @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['188','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ sk_E @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['196'])).

thf('198',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('199',plain,(
    $false ),
    inference(demod,[status(thm)],['133','187','197','198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fM3JBXi886
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:55:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 4.41/4.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.41/4.61  % Solved by: fo/fo7.sh
% 4.41/4.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.41/4.61  % done 3846 iterations in 4.147s
% 4.41/4.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.41/4.61  % SZS output start Refutation
% 4.41/4.61  thf(sk_C_type, type, sk_C: $i).
% 4.41/4.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.41/4.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.41/4.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 4.41/4.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.41/4.61  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 4.41/4.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.41/4.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.41/4.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.41/4.61  thf(sk_A_type, type, sk_A: $i).
% 4.41/4.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.41/4.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.41/4.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.41/4.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.41/4.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.41/4.61  thf(sk_B_type, type, sk_B: $i).
% 4.41/4.61  thf(sk_E_type, type, sk_E: $i).
% 4.41/4.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.41/4.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.41/4.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.41/4.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.41/4.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.41/4.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.41/4.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.41/4.61  thf(sk_D_type, type, sk_D: $i).
% 4.41/4.61  thf(d1_funct_2, axiom,
% 4.41/4.61    (![A:$i,B:$i,C:$i]:
% 4.41/4.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.41/4.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.41/4.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.41/4.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.41/4.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.41/4.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.41/4.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.41/4.61  thf(zf_stmt_0, axiom,
% 4.41/4.61    (![B:$i,A:$i]:
% 4.41/4.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.41/4.61       ( zip_tseitin_0 @ B @ A ) ))).
% 4.41/4.61  thf('0', plain,
% 4.41/4.61      (![X41 : $i, X42 : $i]:
% 4.41/4.61         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.41/4.61  thf('1', plain,
% 4.41/4.61      (![X41 : $i, X42 : $i]:
% 4.41/4.61         ((zip_tseitin_0 @ X41 @ X42) | ((X42) != (k1_xboole_0)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.41/4.61  thf('2', plain, (![X41 : $i]: (zip_tseitin_0 @ X41 @ k1_xboole_0)),
% 4.41/4.61      inference('simplify', [status(thm)], ['1'])).
% 4.41/4.61  thf('3', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.41/4.61         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 4.41/4.61      inference('sup+', [status(thm)], ['0', '2'])).
% 4.41/4.61  thf('4', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 4.41/4.61      inference('eq_fact', [status(thm)], ['3'])).
% 4.41/4.61  thf(t4_subset_1, axiom,
% 4.41/4.61    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.41/4.61  thf('5', plain,
% 4.41/4.61      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 4.41/4.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.41/4.61  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.41/4.61  thf(zf_stmt_2, axiom,
% 4.41/4.61    (![C:$i,B:$i,A:$i]:
% 4.41/4.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.41/4.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.41/4.61  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 4.41/4.61  thf(zf_stmt_4, axiom,
% 4.41/4.61    (![A:$i,B:$i,C:$i]:
% 4.41/4.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.41/4.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.41/4.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.41/4.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.41/4.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.41/4.61  thf('6', plain,
% 4.41/4.61      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.41/4.61         (~ (zip_tseitin_0 @ X46 @ X47)
% 4.41/4.61          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 4.41/4.61          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.41/4.61  thf('7', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 4.41/4.61      inference('sup-', [status(thm)], ['5', '6'])).
% 4.41/4.61  thf('8', plain, (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X0)),
% 4.41/4.61      inference('sup-', [status(thm)], ['4', '7'])).
% 4.41/4.61  thf('9', plain,
% 4.41/4.61      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 4.41/4.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.41/4.61  thf(cc1_partfun1, axiom,
% 4.41/4.61    (![A:$i,B:$i]:
% 4.41/4.61     ( ( v1_xboole_0 @ A ) =>
% 4.41/4.61       ( ![C:$i]:
% 4.41/4.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.41/4.61           ( v1_partfun1 @ C @ A ) ) ) ))).
% 4.41/4.61  thf('10', plain,
% 4.41/4.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.41/4.61         (~ (v1_xboole_0 @ X38)
% 4.41/4.61          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X40)))
% 4.41/4.61          | (v1_partfun1 @ X39 @ X38))),
% 4.41/4.61      inference('cnf', [status(esa)], [cc1_partfun1])).
% 4.41/4.61  thf('11', plain,
% 4.41/4.61      (![X1 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 4.41/4.61      inference('sup-', [status(thm)], ['9', '10'])).
% 4.41/4.61  thf('12', plain,
% 4.41/4.61      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 4.41/4.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.41/4.61  thf(cc1_funct_2, axiom,
% 4.41/4.61    (![A:$i,B:$i,C:$i]:
% 4.41/4.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.41/4.61       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 4.41/4.61         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 4.41/4.61  thf('13', plain,
% 4.41/4.61      (![X35 : $i, X36 : $i, X37 : $i]:
% 4.41/4.61         (~ (v1_funct_1 @ X35)
% 4.41/4.61          | ~ (v1_partfun1 @ X35 @ X36)
% 4.41/4.61          | (v1_funct_2 @ X35 @ X36 @ X37)
% 4.41/4.61          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 4.41/4.61      inference('cnf', [status(esa)], [cc1_funct_2])).
% 4.41/4.61  thf('14', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 4.41/4.61          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 4.41/4.61          | ~ (v1_funct_1 @ k1_xboole_0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['12', '13'])).
% 4.41/4.61  thf(t110_relat_1, axiom,
% 4.41/4.61    (![A:$i]:
% 4.41/4.61     ( ( v1_relat_1 @ A ) =>
% 4.41/4.61       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 4.41/4.61  thf('15', plain,
% 4.41/4.61      (![X16 : $i]:
% 4.41/4.61         (((k7_relat_1 @ X16 @ k1_xboole_0) = (k1_xboole_0))
% 4.41/4.61          | ~ (v1_relat_1 @ X16))),
% 4.41/4.61      inference('cnf', [status(esa)], [t110_relat_1])).
% 4.41/4.61  thf(t178_funct_2, conjecture,
% 4.41/4.61    (![A:$i,B:$i,C:$i,D:$i]:
% 4.41/4.61     ( ( ~( v1_xboole_0 @ D ) ) =>
% 4.41/4.61       ( ![E:$i]:
% 4.41/4.61         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 4.41/4.61             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 4.41/4.61           ( ( ( r1_tarski @ B @ A ) & 
% 4.41/4.61               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 4.41/4.61             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 4.41/4.61               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 4.41/4.61               ( m1_subset_1 @
% 4.41/4.61                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 4.41/4.61                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 4.41/4.61  thf(zf_stmt_5, negated_conjecture,
% 4.41/4.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.41/4.61        ( ( ~( v1_xboole_0 @ D ) ) =>
% 4.41/4.61          ( ![E:$i]:
% 4.41/4.61            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 4.41/4.61                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 4.41/4.61              ( ( ( r1_tarski @ B @ A ) & 
% 4.41/4.61                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 4.41/4.61                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 4.41/4.61                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 4.41/4.61                  ( m1_subset_1 @
% 4.41/4.61                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 4.41/4.61                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 4.41/4.61    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 4.41/4.61  thf('16', plain,
% 4.41/4.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf(dt_k2_partfun1, axiom,
% 4.41/4.61    (![A:$i,B:$i,C:$i,D:$i]:
% 4.41/4.61     ( ( ( v1_funct_1 @ C ) & 
% 4.41/4.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.41/4.61       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 4.41/4.61         ( m1_subset_1 @
% 4.41/4.61           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 4.41/4.61           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 4.41/4.61  thf('17', plain,
% 4.41/4.61      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 4.41/4.61         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 4.41/4.61          | ~ (v1_funct_1 @ X49)
% 4.41/4.61          | (v1_funct_1 @ (k2_partfun1 @ X50 @ X51 @ X49 @ X52)))),
% 4.41/4.61      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 4.41/4.61  thf('18', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 4.41/4.61          | ~ (v1_funct_1 @ sk_E))),
% 4.41/4.61      inference('sup-', [status(thm)], ['16', '17'])).
% 4.41/4.61  thf('19', plain, ((v1_funct_1 @ sk_E)),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('20', plain,
% 4.41/4.61      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['18', '19'])).
% 4.41/4.61  thf('21', plain,
% 4.41/4.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf(redefinition_k2_partfun1, axiom,
% 4.41/4.61    (![A:$i,B:$i,C:$i,D:$i]:
% 4.41/4.61     ( ( ( v1_funct_1 @ C ) & 
% 4.41/4.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.41/4.61       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 4.41/4.61  thf('22', plain,
% 4.41/4.61      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 4.41/4.61         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 4.41/4.61          | ~ (v1_funct_1 @ X53)
% 4.41/4.61          | ((k2_partfun1 @ X54 @ X55 @ X53 @ X56) = (k7_relat_1 @ X53 @ X56)))),
% 4.41/4.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 4.41/4.61  thf('23', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 4.41/4.61          | ~ (v1_funct_1 @ sk_E))),
% 4.41/4.61      inference('sup-', [status(thm)], ['21', '22'])).
% 4.41/4.61  thf('24', plain, ((v1_funct_1 @ sk_E)),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('25', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['23', '24'])).
% 4.41/4.61  thf('26', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['20', '25'])).
% 4.41/4.61  thf('27', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_relat_1 @ sk_E))),
% 4.41/4.61      inference('sup+', [status(thm)], ['15', '26'])).
% 4.41/4.61  thf('28', plain,
% 4.41/4.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf(cc2_relat_1, axiom,
% 4.41/4.61    (![A:$i]:
% 4.41/4.61     ( ( v1_relat_1 @ A ) =>
% 4.41/4.61       ( ![B:$i]:
% 4.41/4.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.41/4.61  thf('29', plain,
% 4.41/4.61      (![X8 : $i, X9 : $i]:
% 4.41/4.61         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 4.41/4.61          | (v1_relat_1 @ X8)
% 4.41/4.61          | ~ (v1_relat_1 @ X9))),
% 4.41/4.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.41/4.61  thf('30', plain,
% 4.41/4.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 4.41/4.61      inference('sup-', [status(thm)], ['28', '29'])).
% 4.41/4.61  thf(fc6_relat_1, axiom,
% 4.41/4.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.41/4.61  thf('31', plain,
% 4.41/4.61      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 4.41/4.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.41/4.61  thf('32', plain, ((v1_relat_1 @ sk_E)),
% 4.41/4.61      inference('demod', [status(thm)], ['30', '31'])).
% 4.41/4.61  thf('33', plain, ((v1_funct_1 @ k1_xboole_0)),
% 4.41/4.61      inference('demod', [status(thm)], ['27', '32'])).
% 4.41/4.61  thf('34', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 4.41/4.61          | ~ (v1_partfun1 @ k1_xboole_0 @ X1))),
% 4.41/4.61      inference('demod', [status(thm)], ['14', '33'])).
% 4.41/4.61  thf('35', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         (~ (v1_xboole_0 @ X0) | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1))),
% 4.41/4.61      inference('sup-', [status(thm)], ['11', '34'])).
% 4.41/4.61  thf('36', plain,
% 4.41/4.61      (![X43 : $i, X44 : $i, X45 : $i]:
% 4.41/4.61         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 4.41/4.61          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 4.41/4.61          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.41/4.61  thf('37', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         (~ (v1_xboole_0 @ X1)
% 4.41/4.61          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 4.41/4.61          | ((X1) = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['35', '36'])).
% 4.41/4.61  thf('38', plain,
% 4.41/4.61      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 4.41/4.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.41/4.61  thf(redefinition_k1_relset_1, axiom,
% 4.41/4.61    (![A:$i,B:$i,C:$i]:
% 4.41/4.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.41/4.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.41/4.61  thf('39', plain,
% 4.41/4.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.41/4.61         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 4.41/4.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 4.41/4.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.41/4.61  thf('40', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['38', '39'])).
% 4.41/4.61  thf(t113_zfmisc_1, axiom,
% 4.41/4.61    (![A:$i,B:$i]:
% 4.41/4.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.41/4.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.41/4.61  thf('41', plain,
% 4.41/4.61      (![X2 : $i, X3 : $i]:
% 4.41/4.61         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 4.41/4.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.41/4.61  thf('42', plain,
% 4.41/4.61      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 4.41/4.61      inference('simplify', [status(thm)], ['41'])).
% 4.41/4.61  thf('43', plain,
% 4.41/4.61      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 4.41/4.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.41/4.61  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.41/4.61      inference('sup+', [status(thm)], ['42', '43'])).
% 4.41/4.61  thf('45', plain,
% 4.41/4.61      (![X16 : $i]:
% 4.41/4.61         (((k7_relat_1 @ X16 @ k1_xboole_0) = (k1_xboole_0))
% 4.41/4.61          | ~ (v1_relat_1 @ X16))),
% 4.41/4.61      inference('cnf', [status(esa)], [t110_relat_1])).
% 4.41/4.61  thf(t87_relat_1, axiom,
% 4.41/4.61    (![A:$i,B:$i]:
% 4.41/4.61     ( ( v1_relat_1 @ B ) =>
% 4.41/4.61       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 4.41/4.61  thf('46', plain,
% 4.41/4.61      (![X21 : $i, X22 : $i]:
% 4.41/4.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X22)) @ X22)
% 4.41/4.61          | ~ (v1_relat_1 @ X21))),
% 4.41/4.61      inference('cnf', [status(esa)], [t87_relat_1])).
% 4.41/4.61  thf(t3_xboole_1, axiom,
% 4.41/4.61    (![A:$i]:
% 4.41/4.61     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.41/4.61  thf('47', plain,
% 4.41/4.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 4.41/4.61      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.41/4.61  thf('48', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (~ (v1_relat_1 @ X0)
% 4.41/4.61          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['46', '47'])).
% 4.41/4.61  thf('49', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 4.41/4.61          | ~ (v1_relat_1 @ X0)
% 4.41/4.61          | ~ (v1_relat_1 @ X0))),
% 4.41/4.61      inference('sup+', [status(thm)], ['45', '48'])).
% 4.41/4.61  thf('50', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (~ (v1_relat_1 @ X0) | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 4.41/4.61      inference('simplify', [status(thm)], ['49'])).
% 4.41/4.61  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['44', '50'])).
% 4.41/4.61  thf('52', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.41/4.61      inference('demod', [status(thm)], ['40', '51'])).
% 4.41/4.61  thf('53', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         (~ (v1_xboole_0 @ X1)
% 4.41/4.61          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 4.41/4.61          | ((X1) = (k1_xboole_0)))),
% 4.41/4.61      inference('demod', [status(thm)], ['37', '52'])).
% 4.41/4.61  thf('54', plain,
% 4.41/4.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['8', '53'])).
% 4.41/4.61  thf('55', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         (~ (v1_xboole_0 @ X0) | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1))),
% 4.41/4.61      inference('sup-', [status(thm)], ['11', '34'])).
% 4.41/4.61  thf('56', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.41/4.61         ((v1_funct_2 @ X0 @ X2 @ X1)
% 4.41/4.61          | ~ (v1_xboole_0 @ X0)
% 4.41/4.61          | ~ (v1_xboole_0 @ X2))),
% 4.41/4.61      inference('sup+', [status(thm)], ['54', '55'])).
% 4.41/4.61  thf('57', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['23', '24'])).
% 4.41/4.61  thf('58', plain,
% 4.41/4.61      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 4.41/4.61        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 4.41/4.61             sk_C)
% 4.41/4.61        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 4.41/4.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('59', plain,
% 4.41/4.61      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))
% 4.41/4.61         <= (~
% 4.41/4.61             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 4.41/4.61               sk_C)))),
% 4.41/4.61      inference('split', [status(esa)], ['58'])).
% 4.41/4.61  thf('60', plain,
% 4.41/4.61      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))
% 4.41/4.61         <= (~
% 4.41/4.61             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 4.41/4.61               sk_C)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['57', '59'])).
% 4.41/4.61  thf('61', plain,
% 4.41/4.61      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B))))
% 4.41/4.61         <= (~
% 4.41/4.61             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 4.41/4.61               sk_C)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['56', '60'])).
% 4.41/4.61  thf('62', plain, ((r1_tarski @ sk_B @ sk_A)),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('63', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('64', plain,
% 4.41/4.61      (![X43 : $i, X44 : $i, X45 : $i]:
% 4.41/4.61         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 4.41/4.61          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 4.41/4.61          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.41/4.61  thf('65', plain,
% 4.41/4.61      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 4.41/4.61        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['63', '64'])).
% 4.41/4.61  thf('66', plain,
% 4.41/4.61      (![X41 : $i, X42 : $i]:
% 4.41/4.61         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.41/4.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.41/4.61  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.41/4.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.41/4.61  thf('68', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.41/4.61      inference('sup+', [status(thm)], ['66', '67'])).
% 4.41/4.61  thf('69', plain,
% 4.41/4.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('70', plain,
% 4.41/4.61      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.41/4.61         (~ (zip_tseitin_0 @ X46 @ X47)
% 4.41/4.61          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 4.41/4.61          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.41/4.61  thf('71', plain,
% 4.41/4.61      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 4.41/4.61      inference('sup-', [status(thm)], ['69', '70'])).
% 4.41/4.61  thf('72', plain,
% 4.41/4.61      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_E @ sk_D @ sk_A))),
% 4.41/4.61      inference('sup-', [status(thm)], ['68', '71'])).
% 4.41/4.61  thf('73', plain, (~ (v1_xboole_0 @ sk_D)),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('74', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 4.41/4.61      inference('clc', [status(thm)], ['72', '73'])).
% 4.41/4.61  thf('75', plain,
% 4.41/4.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('76', plain,
% 4.41/4.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.41/4.61         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 4.41/4.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 4.41/4.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.41/4.61  thf('77', plain,
% 4.41/4.61      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 4.41/4.61      inference('sup-', [status(thm)], ['75', '76'])).
% 4.41/4.61  thf('78', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 4.41/4.61      inference('demod', [status(thm)], ['65', '74', '77'])).
% 4.41/4.61  thf(t91_relat_1, axiom,
% 4.41/4.61    (![A:$i,B:$i]:
% 4.41/4.61     ( ( v1_relat_1 @ B ) =>
% 4.41/4.61       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 4.41/4.61         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 4.41/4.61  thf('79', plain,
% 4.41/4.61      (![X23 : $i, X24 : $i]:
% 4.41/4.61         (~ (r1_tarski @ X23 @ (k1_relat_1 @ X24))
% 4.41/4.61          | ((k1_relat_1 @ (k7_relat_1 @ X24 @ X23)) = (X23))
% 4.41/4.61          | ~ (v1_relat_1 @ X24))),
% 4.41/4.61      inference('cnf', [status(esa)], [t91_relat_1])).
% 4.41/4.61  thf('80', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (~ (r1_tarski @ X0 @ sk_A)
% 4.41/4.61          | ~ (v1_relat_1 @ sk_E)
% 4.41/4.61          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['78', '79'])).
% 4.41/4.61  thf('81', plain, ((v1_relat_1 @ sk_E)),
% 4.41/4.61      inference('demod', [status(thm)], ['30', '31'])).
% 4.41/4.61  thf('82', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (~ (r1_tarski @ X0 @ sk_A)
% 4.41/4.61          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 4.41/4.61      inference('demod', [status(thm)], ['80', '81'])).
% 4.41/4.61  thf('83', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 4.41/4.61      inference('sup-', [status(thm)], ['62', '82'])).
% 4.41/4.61  thf('84', plain,
% 4.41/4.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['8', '53'])).
% 4.41/4.61  thf('85', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['44', '50'])).
% 4.41/4.61  thf('86', plain,
% 4.41/4.61      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.41/4.61      inference('sup+', [status(thm)], ['84', '85'])).
% 4.41/4.61  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.41/4.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.41/4.61  thf('88', plain,
% 4.41/4.61      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 4.41/4.61      inference('sup+', [status(thm)], ['86', '87'])).
% 4.41/4.61  thf('89', plain,
% 4.41/4.61      (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 4.41/4.61      inference('sup+', [status(thm)], ['83', '88'])).
% 4.41/4.61  thf('90', plain,
% 4.41/4.61      ((~ (v1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B)))
% 4.41/4.61         <= (~
% 4.41/4.61             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 4.41/4.61               sk_C)))),
% 4.41/4.61      inference('clc', [status(thm)], ['61', '89'])).
% 4.41/4.61  thf('91', plain,
% 4.41/4.61      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['18', '19'])).
% 4.41/4.61  thf('92', plain,
% 4.41/4.61      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))
% 4.41/4.61         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))))),
% 4.41/4.61      inference('split', [status(esa)], ['58'])).
% 4.41/4.61  thf('93', plain,
% 4.41/4.61      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['91', '92'])).
% 4.41/4.61  thf('94', plain,
% 4.41/4.61      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('95', plain,
% 4.41/4.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf(redefinition_k7_relset_1, axiom,
% 4.41/4.61    (![A:$i,B:$i,C:$i,D:$i]:
% 4.41/4.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.41/4.61       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 4.41/4.61  thf('96', plain,
% 4.41/4.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 4.41/4.61         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.41/4.61          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 4.41/4.61      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 4.41/4.61  thf('97', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['95', '96'])).
% 4.41/4.61  thf('98', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 4.41/4.61      inference('demod', [status(thm)], ['94', '97'])).
% 4.41/4.61  thf(t148_relat_1, axiom,
% 4.41/4.61    (![A:$i,B:$i]:
% 4.41/4.61     ( ( v1_relat_1 @ B ) =>
% 4.41/4.61       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 4.41/4.61  thf('99', plain,
% 4.41/4.61      (![X17 : $i, X18 : $i]:
% 4.41/4.61         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 4.41/4.61          | ~ (v1_relat_1 @ X17))),
% 4.41/4.61      inference('cnf', [status(esa)], [t148_relat_1])).
% 4.41/4.61  thf(d19_relat_1, axiom,
% 4.41/4.61    (![A:$i,B:$i]:
% 4.41/4.61     ( ( v1_relat_1 @ B ) =>
% 4.41/4.61       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.41/4.61  thf('100', plain,
% 4.41/4.61      (![X10 : $i, X11 : $i]:
% 4.41/4.61         (~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 4.41/4.61          | (v5_relat_1 @ X10 @ X11)
% 4.41/4.61          | ~ (v1_relat_1 @ X10))),
% 4.41/4.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.41/4.61  thf('101', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.41/4.61         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 4.41/4.61          | ~ (v1_relat_1 @ X1)
% 4.41/4.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 4.41/4.61          | (v5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))),
% 4.41/4.61      inference('sup-', [status(thm)], ['99', '100'])).
% 4.41/4.61  thf('102', plain,
% 4.41/4.61      (((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C)
% 4.41/4.61        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 4.41/4.61        | ~ (v1_relat_1 @ sk_E))),
% 4.41/4.61      inference('sup-', [status(thm)], ['98', '101'])).
% 4.41/4.61  thf('103', plain,
% 4.41/4.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('104', plain,
% 4.41/4.61      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 4.41/4.61         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 4.41/4.61          | ~ (v1_funct_1 @ X49)
% 4.41/4.61          | (m1_subset_1 @ (k2_partfun1 @ X50 @ X51 @ X49 @ X52) @ 
% 4.41/4.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51))))),
% 4.41/4.61      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 4.41/4.61  thf('105', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 4.41/4.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 4.41/4.61          | ~ (v1_funct_1 @ sk_E))),
% 4.41/4.61      inference('sup-', [status(thm)], ['103', '104'])).
% 4.41/4.61  thf('106', plain, ((v1_funct_1 @ sk_E)),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('107', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 4.41/4.61          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 4.41/4.61      inference('demod', [status(thm)], ['105', '106'])).
% 4.41/4.61  thf('108', plain,
% 4.41/4.61      (![X8 : $i, X9 : $i]:
% 4.41/4.61         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 4.41/4.61          | (v1_relat_1 @ X8)
% 4.41/4.61          | ~ (v1_relat_1 @ X9))),
% 4.41/4.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.41/4.61  thf('109', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D))
% 4.41/4.61          | (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['107', '108'])).
% 4.41/4.61  thf('110', plain,
% 4.41/4.61      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 4.41/4.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.41/4.61  thf('111', plain,
% 4.41/4.61      (![X0 : $i]: (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['109', '110'])).
% 4.41/4.61  thf('112', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['23', '24'])).
% 4.41/4.61  thf('113', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['111', '112'])).
% 4.41/4.61  thf('114', plain, ((v1_relat_1 @ sk_E)),
% 4.41/4.61      inference('demod', [status(thm)], ['30', '31'])).
% 4.41/4.61  thf('115', plain, ((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 4.41/4.61      inference('demod', [status(thm)], ['102', '113', '114'])).
% 4.41/4.61  thf('116', plain,
% 4.41/4.61      (![X10 : $i, X11 : $i]:
% 4.41/4.61         (~ (v5_relat_1 @ X10 @ X11)
% 4.41/4.61          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 4.41/4.61          | ~ (v1_relat_1 @ X10))),
% 4.41/4.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.41/4.61  thf('117', plain,
% 4.41/4.61      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 4.41/4.61        | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C))),
% 4.41/4.61      inference('sup-', [status(thm)], ['115', '116'])).
% 4.41/4.61  thf('118', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['111', '112'])).
% 4.41/4.61  thf('119', plain,
% 4.41/4.61      ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)),
% 4.41/4.61      inference('demod', [status(thm)], ['117', '118'])).
% 4.41/4.61  thf('120', plain,
% 4.41/4.61      (![X21 : $i, X22 : $i]:
% 4.41/4.61         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X22)) @ X22)
% 4.41/4.61          | ~ (v1_relat_1 @ X21))),
% 4.41/4.61      inference('cnf', [status(esa)], [t87_relat_1])).
% 4.41/4.61  thf(t11_relset_1, axiom,
% 4.41/4.61    (![A:$i,B:$i,C:$i]:
% 4.41/4.61     ( ( v1_relat_1 @ C ) =>
% 4.41/4.61       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 4.41/4.61           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 4.41/4.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 4.41/4.61  thf('121', plain,
% 4.41/4.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.41/4.61         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 4.41/4.61          | ~ (r1_tarski @ (k2_relat_1 @ X32) @ X34)
% 4.41/4.61          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 4.41/4.61          | ~ (v1_relat_1 @ X32))),
% 4.41/4.61      inference('cnf', [status(esa)], [t11_relset_1])).
% 4.41/4.61  thf('122', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.41/4.61         (~ (v1_relat_1 @ X1)
% 4.41/4.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 4.41/4.61          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 4.41/4.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 4.41/4.61          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 4.41/4.61      inference('sup-', [status(thm)], ['120', '121'])).
% 4.41/4.61  thf('123', plain,
% 4.41/4.61      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 4.41/4.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 4.41/4.61        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 4.41/4.61        | ~ (v1_relat_1 @ sk_E))),
% 4.41/4.61      inference('sup-', [status(thm)], ['119', '122'])).
% 4.41/4.61  thf('124', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['111', '112'])).
% 4.41/4.61  thf('125', plain, ((v1_relat_1 @ sk_E)),
% 4.41/4.61      inference('demod', [status(thm)], ['30', '31'])).
% 4.41/4.61  thf('126', plain,
% 4.41/4.61      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 4.41/4.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.41/4.61      inference('demod', [status(thm)], ['123', '124', '125'])).
% 4.41/4.61  thf('127', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['23', '24'])).
% 4.41/4.61  thf('128', plain,
% 4.41/4.61      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 4.41/4.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 4.41/4.61         <= (~
% 4.41/4.61             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 4.41/4.61               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 4.41/4.61      inference('split', [status(esa)], ['58'])).
% 4.41/4.61  thf('129', plain,
% 4.41/4.61      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 4.41/4.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 4.41/4.61         <= (~
% 4.41/4.61             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 4.41/4.61               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 4.41/4.61      inference('sup-', [status(thm)], ['127', '128'])).
% 4.41/4.61  thf('130', plain,
% 4.41/4.61      (((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 4.41/4.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 4.41/4.61      inference('sup-', [status(thm)], ['126', '129'])).
% 4.41/4.61  thf('131', plain,
% 4.41/4.61      (~
% 4.41/4.61       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C)) | 
% 4.41/4.61       ~
% 4.41/4.61       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 4.41/4.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))) | 
% 4.41/4.61       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 4.41/4.61      inference('split', [status(esa)], ['58'])).
% 4.41/4.61  thf('132', plain,
% 4.41/4.61      (~
% 4.41/4.61       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 4.41/4.61      inference('sat_resolution*', [status(thm)], ['93', '130', '131'])).
% 4.41/4.61  thf('133', plain, (~ (v1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B))),
% 4.41/4.61      inference('simpl_trail', [status(thm)], ['90', '132'])).
% 4.41/4.61  thf('134', plain,
% 4.41/4.61      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('135', plain,
% 4.41/4.61      (![X41 : $i, X42 : $i]:
% 4.41/4.61         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.41/4.61  thf('136', plain,
% 4.41/4.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 4.41/4.61      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.41/4.61  thf('137', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.41/4.61         (~ (r1_tarski @ X1 @ X0)
% 4.41/4.61          | (zip_tseitin_0 @ X0 @ X2)
% 4.41/4.61          | ((X1) = (k1_xboole_0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['135', '136'])).
% 4.41/4.61  thf('138', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (((k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) = (k1_xboole_0))
% 4.41/4.61          | (zip_tseitin_0 @ sk_C @ X0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['134', '137'])).
% 4.41/4.61  thf('139', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['95', '96'])).
% 4.41/4.61  thf('140', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (((k9_relat_1 @ sk_E @ sk_B) = (k1_xboole_0))
% 4.41/4.61          | (zip_tseitin_0 @ sk_C @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['138', '139'])).
% 4.41/4.61  thf('141', plain, ((r1_tarski @ sk_B @ sk_A)),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.41/4.61  thf('142', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 4.41/4.61      inference('demod', [status(thm)], ['65', '74', '77'])).
% 4.41/4.61  thf(t152_relat_1, axiom,
% 4.41/4.61    (![A:$i,B:$i]:
% 4.41/4.61     ( ( v1_relat_1 @ B ) =>
% 4.41/4.61       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.41/4.61            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 4.41/4.61            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 4.41/4.61  thf('143', plain,
% 4.41/4.61      (![X19 : $i, X20 : $i]:
% 4.41/4.61         (((X19) = (k1_xboole_0))
% 4.41/4.61          | ~ (v1_relat_1 @ X20)
% 4.41/4.61          | ~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 4.41/4.61          | ((k9_relat_1 @ X20 @ X19) != (k1_xboole_0)))),
% 4.41/4.61      inference('cnf', [status(esa)], [t152_relat_1])).
% 4.41/4.61  thf('144', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (~ (r1_tarski @ X0 @ sk_A)
% 4.41/4.61          | ((k9_relat_1 @ sk_E @ X0) != (k1_xboole_0))
% 4.41/4.61          | ~ (v1_relat_1 @ sk_E)
% 4.41/4.61          | ((X0) = (k1_xboole_0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['142', '143'])).
% 4.41/4.61  thf('145', plain, ((v1_relat_1 @ sk_E)),
% 4.41/4.61      inference('demod', [status(thm)], ['30', '31'])).
% 4.41/4.61  thf('146', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (~ (r1_tarski @ X0 @ sk_A)
% 4.41/4.61          | ((k9_relat_1 @ sk_E @ X0) != (k1_xboole_0))
% 4.41/4.61          | ((X0) = (k1_xboole_0)))),
% 4.41/4.61      inference('demod', [status(thm)], ['144', '145'])).
% 4.41/4.61  thf('147', plain,
% 4.41/4.61      ((((sk_B) = (k1_xboole_0))
% 4.41/4.61        | ((k9_relat_1 @ sk_E @ sk_B) != (k1_xboole_0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['141', '146'])).
% 4.41/4.61  thf('148', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (((k1_xboole_0) != (k1_xboole_0))
% 4.41/4.61          | (zip_tseitin_0 @ sk_C @ X0)
% 4.41/4.61          | ((sk_B) = (k1_xboole_0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['140', '147'])).
% 4.41/4.61  thf('149', plain,
% 4.41/4.61      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C @ X0))),
% 4.41/4.61      inference('simplify', [status(thm)], ['148'])).
% 4.41/4.61  thf('150', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 4.41/4.61      inference('sup-', [status(thm)], ['5', '6'])).
% 4.41/4.61  thf('151', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ k1_xboole_0 @ sk_C @ X0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['149', '150'])).
% 4.41/4.61  thf('152', plain,
% 4.41/4.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['8', '53'])).
% 4.41/4.61  thf('153', plain,
% 4.41/4.61      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.41/4.61         (((X46) != (k1_xboole_0))
% 4.41/4.61          | ((X47) = (k1_xboole_0))
% 4.41/4.61          | (v1_funct_2 @ X48 @ X47 @ X46)
% 4.41/4.61          | ((X48) != (k1_xboole_0))
% 4.41/4.61          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.41/4.61  thf('154', plain,
% 4.41/4.61      (![X47 : $i]:
% 4.41/4.61         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 4.41/4.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ k1_xboole_0)))
% 4.41/4.61          | (v1_funct_2 @ k1_xboole_0 @ X47 @ k1_xboole_0)
% 4.41/4.61          | ((X47) = (k1_xboole_0)))),
% 4.41/4.61      inference('simplify', [status(thm)], ['153'])).
% 4.41/4.61  thf('155', plain,
% 4.41/4.61      (![X2 : $i, X3 : $i]:
% 4.41/4.61         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 4.41/4.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.41/4.61  thf('156', plain,
% 4.41/4.61      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 4.41/4.61      inference('simplify', [status(thm)], ['155'])).
% 4.41/4.61  thf('157', plain,
% 4.41/4.61      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 4.41/4.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.41/4.61  thf('158', plain,
% 4.41/4.61      (![X47 : $i]:
% 4.41/4.61         ((v1_funct_2 @ k1_xboole_0 @ X47 @ k1_xboole_0)
% 4.41/4.61          | ((X47) = (k1_xboole_0)))),
% 4.41/4.61      inference('demod', [status(thm)], ['154', '156', '157'])).
% 4.41/4.61  thf('159', plain,
% 4.41/4.61      (![X43 : $i, X44 : $i, X45 : $i]:
% 4.41/4.61         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 4.41/4.61          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 4.41/4.61          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.41/4.61  thf('160', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (((X0) = (k1_xboole_0))
% 4.41/4.61          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.41/4.61          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['158', '159'])).
% 4.41/4.61  thf('161', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.41/4.61      inference('demod', [status(thm)], ['40', '51'])).
% 4.41/4.61  thf('162', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (((X0) = (k1_xboole_0))
% 4.41/4.61          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.41/4.61          | ((X0) = (k1_xboole_0)))),
% 4.41/4.61      inference('demod', [status(thm)], ['160', '161'])).
% 4.41/4.61  thf('163', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.41/4.61          | ((X0) = (k1_xboole_0)))),
% 4.41/4.61      inference('simplify', [status(thm)], ['162'])).
% 4.41/4.61  thf('164', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 4.41/4.61          | ~ (v1_xboole_0 @ X0)
% 4.41/4.61          | ((X1) = (k1_xboole_0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['152', '163'])).
% 4.41/4.61  thf('165', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (((sk_B) = (k1_xboole_0))
% 4.41/4.61          | ((X0) = (k1_xboole_0))
% 4.41/4.61          | ~ (v1_xboole_0 @ sk_C))),
% 4.41/4.61      inference('sup-', [status(thm)], ['151', '164'])).
% 4.41/4.61  thf('166', plain, ((((sk_B) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C))),
% 4.41/4.61      inference('condensation', [status(thm)], ['165'])).
% 4.41/4.61  thf('167', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.41/4.61      inference('sup+', [status(thm)], ['66', '67'])).
% 4.41/4.61  thf('168', plain,
% 4.41/4.61      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 4.41/4.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.41/4.61      inference('demod', [status(thm)], ['123', '124', '125'])).
% 4.41/4.61  thf('169', plain,
% 4.41/4.61      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.41/4.61         (~ (zip_tseitin_0 @ X46 @ X47)
% 4.41/4.61          | (zip_tseitin_1 @ X48 @ X46 @ X47)
% 4.41/4.61          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.41/4.61  thf('170', plain,
% 4.41/4.61      (((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 4.41/4.61        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 4.41/4.61      inference('sup-', [status(thm)], ['168', '169'])).
% 4.41/4.61  thf('171', plain,
% 4.41/4.61      (((v1_xboole_0 @ sk_C)
% 4.41/4.61        | (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 4.41/4.61      inference('sup-', [status(thm)], ['167', '170'])).
% 4.41/4.61  thf('172', plain,
% 4.41/4.61      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 4.41/4.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.41/4.61      inference('demod', [status(thm)], ['123', '124', '125'])).
% 4.41/4.61  thf('173', plain,
% 4.41/4.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.41/4.61         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 4.41/4.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 4.41/4.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.41/4.61  thf('174', plain,
% 4.41/4.61      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B))
% 4.41/4.61         = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['172', '173'])).
% 4.41/4.61  thf('175', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 4.41/4.61      inference('sup-', [status(thm)], ['62', '82'])).
% 4.41/4.61  thf('176', plain,
% 4.41/4.61      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 4.41/4.61      inference('demod', [status(thm)], ['174', '175'])).
% 4.41/4.61  thf('177', plain,
% 4.41/4.61      (![X43 : $i, X44 : $i, X45 : $i]:
% 4.41/4.61         (((X43) != (k1_relset_1 @ X43 @ X44 @ X45))
% 4.41/4.61          | (v1_funct_2 @ X45 @ X43 @ X44)
% 4.41/4.61          | ~ (zip_tseitin_1 @ X45 @ X44 @ X43))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.41/4.61  thf('178', plain,
% 4.41/4.61      ((((sk_B) != (sk_B))
% 4.41/4.61        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 4.41/4.61        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 4.41/4.61      inference('sup-', [status(thm)], ['176', '177'])).
% 4.41/4.61  thf('179', plain,
% 4.41/4.61      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 4.41/4.61        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 4.41/4.61      inference('simplify', [status(thm)], ['178'])).
% 4.41/4.61  thf('180', plain,
% 4.41/4.61      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))
% 4.41/4.61         <= (~
% 4.41/4.61             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 4.41/4.61               sk_C)))),
% 4.41/4.61      inference('split', [status(esa)], ['58'])).
% 4.41/4.61  thf('181', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 4.41/4.61      inference('demod', [status(thm)], ['23', '24'])).
% 4.41/4.61  thf('182', plain,
% 4.41/4.61      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))
% 4.41/4.61         <= (~
% 4.41/4.61             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 4.41/4.61               sk_C)))),
% 4.41/4.61      inference('demod', [status(thm)], ['180', '181'])).
% 4.41/4.61  thf('183', plain,
% 4.41/4.61      (~
% 4.41/4.61       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 4.41/4.61      inference('sat_resolution*', [status(thm)], ['93', '130', '131'])).
% 4.41/4.61  thf('184', plain,
% 4.41/4.61      (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 4.41/4.61      inference('simpl_trail', [status(thm)], ['182', '183'])).
% 4.41/4.61  thf('185', plain,
% 4.41/4.61      (~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)),
% 4.41/4.61      inference('clc', [status(thm)], ['179', '184'])).
% 4.41/4.61  thf('186', plain, ((v1_xboole_0 @ sk_C)),
% 4.41/4.61      inference('sup-', [status(thm)], ['171', '185'])).
% 4.41/4.61  thf('187', plain, (((sk_B) = (k1_xboole_0))),
% 4.41/4.61      inference('demod', [status(thm)], ['166', '186'])).
% 4.41/4.61  thf('188', plain, ((v1_relat_1 @ sk_E)),
% 4.41/4.61      inference('demod', [status(thm)], ['30', '31'])).
% 4.41/4.61  thf('189', plain,
% 4.41/4.61      (![X41 : $i, X42 : $i]:
% 4.41/4.61         ((zip_tseitin_0 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 4.41/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.41/4.61  thf('190', plain,
% 4.41/4.61      (![X16 : $i]:
% 4.41/4.61         (((k7_relat_1 @ X16 @ k1_xboole_0) = (k1_xboole_0))
% 4.41/4.61          | ~ (v1_relat_1 @ X16))),
% 4.41/4.61      inference('cnf', [status(esa)], [t110_relat_1])).
% 4.41/4.61  thf('191', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.41/4.61         (((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 4.41/4.61          | (zip_tseitin_0 @ X0 @ X2)
% 4.41/4.61          | ~ (v1_relat_1 @ X1))),
% 4.41/4.61      inference('sup+', [status(thm)], ['189', '190'])).
% 4.41/4.61  thf('192', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         ((zip_tseitin_0 @ X1 @ X0)
% 4.41/4.61          | ((k7_relat_1 @ sk_E @ X1) = (k1_xboole_0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['188', '191'])).
% 4.41/4.61  thf('193', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 4.41/4.61      inference('sup-', [status(thm)], ['5', '6'])).
% 4.41/4.61  thf('194', plain,
% 4.41/4.61      (![X0 : $i, X1 : $i]:
% 4.41/4.61         (((k7_relat_1 @ sk_E @ X1) = (k1_xboole_0))
% 4.41/4.61          | (zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0))),
% 4.41/4.61      inference('sup-', [status(thm)], ['192', '193'])).
% 4.41/4.61  thf('195', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.41/4.61          | ((X0) = (k1_xboole_0)))),
% 4.41/4.61      inference('simplify', [status(thm)], ['162'])).
% 4.41/4.61  thf('196', plain,
% 4.41/4.61      (![X0 : $i]:
% 4.41/4.61         (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 4.41/4.61          | ((X0) = (k1_xboole_0)))),
% 4.41/4.61      inference('sup-', [status(thm)], ['194', '195'])).
% 4.41/4.61  thf('197', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 4.41/4.61      inference('condensation', [status(thm)], ['196'])).
% 4.41/4.61  thf('198', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.41/4.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.41/4.61  thf('199', plain, ($false),
% 4.41/4.61      inference('demod', [status(thm)], ['133', '187', '197', '198'])).
% 4.41/4.61  
% 4.41/4.61  % SZS output end Refutation
% 4.41/4.61  
% 4.41/4.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
