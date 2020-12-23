%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TbJHiZlnfA

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:07 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  262 (1085 expanded)
%              Number of leaves         :   51 ( 333 expanded)
%              Depth                    :   23
%              Number of atoms          : 1815 (12471 expanded)
%              Number of equality atoms :  169 ( 924 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(zf_stmt_0,negated_conjecture,(
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

thf('0',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_relat_1 @ X23 @ X24 )
      | ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X43 ) @ X44 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X43 ) @ X45 )
      | ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X49: $i,X50: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('24',plain,(
    ! [X30: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( zip_tseitin_0 @ X54 @ X55 )
      | ( zip_tseitin_1 @ X56 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k6_relat_1 @ sk_B_2 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ( X51
        = ( k1_relset_1 @ X51 @ X52 @ X53 ) )
      | ~ ( zip_tseitin_1 @ X53 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k6_relat_1 @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X49: $i,X50: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X30: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X25: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('50',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('54',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t31_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
       => ( ( B
            = ( k1_relset_1 @ B @ A @ C ) )
          & ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) )).

thf('57',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X46 ) @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X48 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[t31_relset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('60',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('64',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X1 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X1 ) @ X0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k6_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k6_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','70'])).

thf('72',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('81',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51
       != ( k1_relset_1 @ X51 @ X52 @ X53 ) )
      | ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ~ ( zip_tseitin_1 @ X53 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X49: $i,X50: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 )
      | ( X50 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,(
    ! [X49: $i] :
      ( zip_tseitin_0 @ X49 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('87',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( zip_tseitin_0 @ X54 @ X55 )
      | ( zip_tseitin_1 @ X56 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['83','89'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('91',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('92',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('102',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('104',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['77'])).

thf('105',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','106'])).

thf('108',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('109',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('110',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['77'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['77'])).

thf('116',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('117',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['79','107','114','115','116'])).

thf('118',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['75','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['73','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54 != k1_xboole_0 )
      | ( X55 = k1_xboole_0 )
      | ( v1_funct_2 @ X56 @ X55 @ X54 )
      | ( X56 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('123',plain,(
    ! [X55: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X55 @ k1_xboole_0 )
      | ( X55 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('125',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('127',plain,(
    ! [X55: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X55 @ k1_xboole_0 )
      | ( X55 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['123','125','126'])).

thf('128',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ( X51
        = ( k1_relset_1 @ X51 @ X52 @ X53 ) )
      | ~ ( zip_tseitin_1 @ X53 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','132'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(condensation,[status(thm)],['136'])).

thf('138',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','137'])).

thf('139',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51
       != ( k1_relset_1 @ X51 @ X52 @ X53 ) )
      | ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ~ ( zip_tseitin_1 @ X53 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('140',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['77'])).

thf('143',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('144',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['77'])).

thf('145',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['77'])).

thf('147',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['79','145','146'])).

thf('148',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['142','147'])).

thf('149',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['141','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('151',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( zip_tseitin_0 @ X54 @ X55 )
      | ( zip_tseitin_1 @ X56 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('152',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['0','3'])).

thf('154',plain,(
    ! [X49: $i,X50: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('155',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('156',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['154','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','158'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('160',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('163',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('167',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['83','89'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['165','168'])).

thf('170',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['77'])).

thf('171',plain,
    ( ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('173',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ ( k1_relat_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('176',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('177',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_relat_1 @ X23 @ X24 )
      | ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ( k6_relat_1 @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('185',plain,(
    ! [X30: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('187',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['185','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['184','189'])).

thf('191',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r1_tarski @ X0 @ sk_B_2 )
      | ( X0 = sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B_2 @ X0 ) )
        = sk_B_2 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['183','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['174','195'])).

thf('197',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = sk_B_2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['75','117'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X25: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(condensation,[status(thm)],['202'])).

thf('204',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['171','203'])).

thf('205',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_C_1 @ X0 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['164','204'])).

thf('206',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['79','145','146'])).

thf('207',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference(simpl_trail,[status(thm)],['205','206'])).

thf('208',plain,(
    zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['152','207'])).

thf('209',plain,(
    $false ),
    inference(demod,[status(thm)],['149','208'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TbJHiZlnfA
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.15/2.36  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.15/2.36  % Solved by: fo/fo7.sh
% 2.15/2.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.15/2.36  % done 3064 iterations in 1.899s
% 2.15/2.36  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.15/2.36  % SZS output start Refutation
% 2.15/2.36  thf(sk_A_type, type, sk_A: $i).
% 2.15/2.36  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.15/2.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.15/2.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.15/2.36  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.15/2.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.15/2.36  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.15/2.36  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.15/2.36  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.15/2.36  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.15/2.36  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.15/2.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.15/2.36  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.15/2.36  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.15/2.36  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.15/2.36  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.15/2.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.15/2.36  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.15/2.36  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.15/2.36  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.15/2.36  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.15/2.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.15/2.36  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 2.15/2.36  thf(sk_D_type, type, sk_D: $i).
% 2.15/2.36  thf(t8_funct_2, conjecture,
% 2.15/2.36    (![A:$i,B:$i,C:$i,D:$i]:
% 2.15/2.36     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.15/2.36         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.15/2.36       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 2.15/2.36         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.15/2.36           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 2.15/2.36             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 2.15/2.36  thf(zf_stmt_0, negated_conjecture,
% 2.15/2.36    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.15/2.36        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.15/2.36            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.15/2.36          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 2.15/2.36            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.15/2.36              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 2.15/2.36                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 2.15/2.36    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 2.15/2.36  thf('0', plain,
% 2.15/2.36      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_D) @ sk_C_1)),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf('1', plain,
% 2.15/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf(redefinition_k2_relset_1, axiom,
% 2.15/2.36    (![A:$i,B:$i,C:$i]:
% 2.15/2.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.15/2.36       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.15/2.36  thf('2', plain,
% 2.15/2.36      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.15/2.36         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 2.15/2.36          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 2.15/2.36      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.15/2.36  thf('3', plain,
% 2.15/2.36      (((k2_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.15/2.36      inference('sup-', [status(thm)], ['1', '2'])).
% 2.15/2.36  thf('4', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 2.15/2.36      inference('demod', [status(thm)], ['0', '3'])).
% 2.15/2.36  thf('5', plain,
% 2.15/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf(cc2_relset_1, axiom,
% 2.15/2.36    (![A:$i,B:$i,C:$i]:
% 2.15/2.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.15/2.36       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.15/2.36  thf('6', plain,
% 2.15/2.36      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.15/2.36         ((v4_relat_1 @ X34 @ X35)
% 2.15/2.36          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.15/2.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.15/2.36  thf('7', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 2.15/2.36      inference('sup-', [status(thm)], ['5', '6'])).
% 2.15/2.36  thf(d18_relat_1, axiom,
% 2.15/2.36    (![A:$i,B:$i]:
% 2.15/2.36     ( ( v1_relat_1 @ B ) =>
% 2.15/2.36       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.15/2.36  thf('8', plain,
% 2.15/2.36      (![X23 : $i, X24 : $i]:
% 2.15/2.36         (~ (v4_relat_1 @ X23 @ X24)
% 2.15/2.36          | (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 2.15/2.36          | ~ (v1_relat_1 @ X23))),
% 2.15/2.36      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.15/2.36  thf('9', plain,
% 2.15/2.36      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 2.15/2.36      inference('sup-', [status(thm)], ['7', '8'])).
% 2.15/2.36  thf('10', plain,
% 2.15/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf(cc2_relat_1, axiom,
% 2.15/2.36    (![A:$i]:
% 2.15/2.36     ( ( v1_relat_1 @ A ) =>
% 2.15/2.36       ( ![B:$i]:
% 2.15/2.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.15/2.36  thf('11', plain,
% 2.15/2.36      (![X21 : $i, X22 : $i]:
% 2.15/2.36         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 2.15/2.36          | (v1_relat_1 @ X21)
% 2.15/2.36          | ~ (v1_relat_1 @ X22))),
% 2.15/2.36      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.15/2.36  thf('12', plain,
% 2.15/2.36      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | (v1_relat_1 @ sk_D))),
% 2.15/2.36      inference('sup-', [status(thm)], ['10', '11'])).
% 2.15/2.36  thf(fc6_relat_1, axiom,
% 2.15/2.36    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.15/2.36  thf('13', plain,
% 2.15/2.36      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 2.15/2.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.15/2.36  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 2.15/2.36      inference('demod', [status(thm)], ['12', '13'])).
% 2.15/2.36  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 2.15/2.36      inference('demod', [status(thm)], ['9', '14'])).
% 2.15/2.36  thf(t11_relset_1, axiom,
% 2.15/2.36    (![A:$i,B:$i,C:$i]:
% 2.15/2.36     ( ( v1_relat_1 @ C ) =>
% 2.15/2.36       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 2.15/2.36           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 2.15/2.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 2.15/2.36  thf('16', plain,
% 2.15/2.36      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.15/2.36         (~ (r1_tarski @ (k1_relat_1 @ X43) @ X44)
% 2.15/2.36          | ~ (r1_tarski @ (k2_relat_1 @ X43) @ X45)
% 2.15/2.36          | (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.15/2.36          | ~ (v1_relat_1 @ X43))),
% 2.15/2.36      inference('cnf', [status(esa)], [t11_relset_1])).
% 2.15/2.36  thf('17', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (~ (v1_relat_1 @ sk_D)
% 2.15/2.36          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.15/2.36          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['15', '16'])).
% 2.15/2.36  thf('18', plain, ((v1_relat_1 @ sk_D)),
% 2.15/2.36      inference('demod', [status(thm)], ['12', '13'])).
% 2.15/2.36  thf('19', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.15/2.36          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 2.15/2.36      inference('demod', [status(thm)], ['17', '18'])).
% 2.15/2.36  thf('20', plain,
% 2.15/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['4', '19'])).
% 2.15/2.36  thf(redefinition_k1_relset_1, axiom,
% 2.15/2.36    (![A:$i,B:$i,C:$i]:
% 2.15/2.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.15/2.36       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.15/2.36  thf('21', plain,
% 2.15/2.36      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.15/2.36         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 2.15/2.36          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 2.15/2.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.15/2.36  thf('22', plain,
% 2.15/2.36      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.15/2.36      inference('sup-', [status(thm)], ['20', '21'])).
% 2.15/2.36  thf(d1_funct_2, axiom,
% 2.15/2.36    (![A:$i,B:$i,C:$i]:
% 2.15/2.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.15/2.36       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.15/2.36           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.15/2.36             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.15/2.36         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.15/2.36           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.15/2.36             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.15/2.36  thf(zf_stmt_1, axiom,
% 2.15/2.36    (![B:$i,A:$i]:
% 2.15/2.36     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.15/2.36       ( zip_tseitin_0 @ B @ A ) ))).
% 2.15/2.36  thf('23', plain,
% 2.15/2.36      (![X49 : $i, X50 : $i]:
% 2.15/2.36         ((zip_tseitin_0 @ X49 @ X50) | ((X49) = (k1_xboole_0)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.15/2.36  thf(t71_relat_1, axiom,
% 2.15/2.36    (![A:$i]:
% 2.15/2.36     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.15/2.36       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.15/2.36  thf('24', plain, (![X30 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 2.15/2.36      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.15/2.36  thf(t64_relat_1, axiom,
% 2.15/2.36    (![A:$i]:
% 2.15/2.36     ( ( v1_relat_1 @ A ) =>
% 2.15/2.36       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 2.15/2.36           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.15/2.36         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 2.15/2.36  thf('25', plain,
% 2.15/2.36      (![X29 : $i]:
% 2.15/2.36         (((k1_relat_1 @ X29) != (k1_xboole_0))
% 2.15/2.36          | ((X29) = (k1_xboole_0))
% 2.15/2.36          | ~ (v1_relat_1 @ X29))),
% 2.15/2.36      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.15/2.36  thf('26', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (((X0) != (k1_xboole_0))
% 2.15/2.36          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.15/2.36          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['24', '25'])).
% 2.15/2.36  thf(fc3_funct_1, axiom,
% 2.15/2.36    (![A:$i]:
% 2.15/2.36     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.15/2.36       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.15/2.36  thf('27', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 2.15/2.36      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.15/2.36  thf('28', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('demod', [status(thm)], ['26', '27'])).
% 2.15/2.36  thf('29', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.15/2.36      inference('simplify', [status(thm)], ['28'])).
% 2.15/2.36  thf('30', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         (((k6_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 2.15/2.36      inference('sup+', [status(thm)], ['23', '29'])).
% 2.15/2.36  thf('31', plain,
% 2.15/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.15/2.36  thf(zf_stmt_3, axiom,
% 2.15/2.36    (![C:$i,B:$i,A:$i]:
% 2.15/2.36     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.15/2.36       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.15/2.36  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.15/2.36  thf(zf_stmt_5, axiom,
% 2.15/2.36    (![A:$i,B:$i,C:$i]:
% 2.15/2.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.15/2.36       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.15/2.36         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.15/2.36           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.15/2.36             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.15/2.36  thf('32', plain,
% 2.15/2.36      (![X54 : $i, X55 : $i, X56 : $i]:
% 2.15/2.36         (~ (zip_tseitin_0 @ X54 @ X55)
% 2.15/2.36          | (zip_tseitin_1 @ X56 @ X54 @ X55)
% 2.15/2.36          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54))))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.15/2.36  thf('33', plain,
% 2.15/2.36      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 2.15/2.36        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 2.15/2.36      inference('sup-', [status(thm)], ['31', '32'])).
% 2.15/2.36  thf('34', plain,
% 2.15/2.36      ((((k6_relat_1 @ sk_B_2) = (k1_xboole_0))
% 2.15/2.36        | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 2.15/2.36      inference('sup-', [status(thm)], ['30', '33'])).
% 2.15/2.36  thf('35', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf('36', plain,
% 2.15/2.36      (![X51 : $i, X52 : $i, X53 : $i]:
% 2.15/2.36         (~ (v1_funct_2 @ X53 @ X51 @ X52)
% 2.15/2.36          | ((X51) = (k1_relset_1 @ X51 @ X52 @ X53))
% 2.15/2.36          | ~ (zip_tseitin_1 @ X53 @ X52 @ X51))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.15/2.36  thf('37', plain,
% 2.15/2.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 2.15/2.36        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['35', '36'])).
% 2.15/2.36  thf('38', plain,
% 2.15/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf('39', plain,
% 2.15/2.36      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.15/2.36         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 2.15/2.36          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 2.15/2.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.15/2.36  thf('40', plain,
% 2.15/2.36      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.15/2.36      inference('sup-', [status(thm)], ['38', '39'])).
% 2.15/2.36  thf('41', plain,
% 2.15/2.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 2.15/2.36        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.15/2.36      inference('demod', [status(thm)], ['37', '40'])).
% 2.15/2.36  thf('42', plain,
% 2.15/2.36      ((((k6_relat_1 @ sk_B_2) = (k1_xboole_0))
% 2.15/2.36        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['34', '41'])).
% 2.15/2.36  thf('43', plain,
% 2.15/2.36      (![X49 : $i, X50 : $i]:
% 2.15/2.36         ((zip_tseitin_0 @ X49 @ X50) | ((X49) = (k1_xboole_0)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.15/2.36  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.15/2.36  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.15/2.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.15/2.36  thf('45', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.15/2.36      inference('sup+', [status(thm)], ['43', '44'])).
% 2.15/2.36  thf(d10_xboole_0, axiom,
% 2.15/2.36    (![A:$i,B:$i]:
% 2.15/2.36     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.15/2.36  thf('46', plain,
% 2.15/2.36      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 2.15/2.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.15/2.36  thf('47', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 2.15/2.36      inference('simplify', [status(thm)], ['46'])).
% 2.15/2.36  thf('48', plain, (![X30 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 2.15/2.36      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.15/2.36  thf(fc10_relat_1, axiom,
% 2.15/2.36    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 2.15/2.36  thf('49', plain,
% 2.15/2.36      (![X25 : $i]:
% 2.15/2.36         ((v1_xboole_0 @ (k1_relat_1 @ X25)) | ~ (v1_xboole_0 @ X25))),
% 2.15/2.36      inference('cnf', [status(esa)], [fc10_relat_1])).
% 2.15/2.36  thf(t7_xboole_0, axiom,
% 2.15/2.36    (![A:$i]:
% 2.15/2.36     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.15/2.36          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.15/2.36  thf('50', plain,
% 2.15/2.36      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 2.15/2.36      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.15/2.36  thf(d1_xboole_0, axiom,
% 2.15/2.36    (![A:$i]:
% 2.15/2.36     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.15/2.36  thf('51', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.15/2.36      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.15/2.36  thf('52', plain,
% 2.15/2.36      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['50', '51'])).
% 2.15/2.36  thf('53', plain,
% 2.15/2.36      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['49', '52'])).
% 2.15/2.36  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.15/2.36  thf('54', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 2.15/2.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.15/2.36  thf(t3_subset, axiom,
% 2.15/2.36    (![A:$i,B:$i]:
% 2.15/2.36     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.15/2.36  thf('55', plain,
% 2.15/2.36      (![X15 : $i, X17 : $i]:
% 2.15/2.36         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 2.15/2.36      inference('cnf', [status(esa)], [t3_subset])).
% 2.15/2.36  thf('56', plain,
% 2.15/2.36      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['54', '55'])).
% 2.15/2.36  thf(t31_relset_1, axiom,
% 2.15/2.36    (![A:$i,B:$i,C:$i]:
% 2.15/2.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.15/2.36       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 2.15/2.36         ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 2.15/2.36           ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ))).
% 2.15/2.36  thf('57', plain,
% 2.15/2.36      (![X46 : $i, X47 : $i, X48 : $i]:
% 2.15/2.36         (~ (r1_tarski @ (k6_relat_1 @ X46) @ X47)
% 2.15/2.36          | ((X46) = (k1_relset_1 @ X46 @ X48 @ X47))
% 2.15/2.36          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X48))))),
% 2.15/2.36      inference('cnf', [status(esa)], [t31_relset_1])).
% 2.15/2.36  thf('58', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         (((X1) = (k1_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 2.15/2.36          | ~ (r1_tarski @ (k6_relat_1 @ X1) @ k1_xboole_0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['56', '57'])).
% 2.15/2.36  thf('59', plain,
% 2.15/2.36      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['54', '55'])).
% 2.15/2.36  thf('60', plain,
% 2.15/2.36      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.15/2.36         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 2.15/2.36          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 2.15/2.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.15/2.36  thf('61', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['59', '60'])).
% 2.15/2.36  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.15/2.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.15/2.36  thf('63', plain,
% 2.15/2.36      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['49', '52'])).
% 2.15/2.36  thf('64', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['62', '63'])).
% 2.15/2.36  thf('65', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.15/2.36      inference('demod', [status(thm)], ['61', '64'])).
% 2.15/2.36  thf('66', plain,
% 2.15/2.36      (![X1 : $i]:
% 2.15/2.36         (((X1) = (k1_xboole_0))
% 2.15/2.36          | ~ (r1_tarski @ (k6_relat_1 @ X1) @ k1_xboole_0))),
% 2.15/2.36      inference('demod', [status(thm)], ['58', '65'])).
% 2.15/2.36  thf('67', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         (~ (r1_tarski @ (k6_relat_1 @ X1) @ (k1_relat_1 @ X0))
% 2.15/2.36          | ~ (v1_xboole_0 @ X0)
% 2.15/2.36          | ((X1) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['53', '66'])).
% 2.15/2.36  thf('68', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         (~ (r1_tarski @ (k6_relat_1 @ X1) @ X0)
% 2.15/2.36          | ((X1) = (k1_xboole_0))
% 2.15/2.36          | ~ (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['48', '67'])).
% 2.15/2.36  thf('69', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (~ (v1_xboole_0 @ (k6_relat_1 @ (k6_relat_1 @ X0)))
% 2.15/2.36          | ((X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['47', '68'])).
% 2.15/2.36  thf('70', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         ((zip_tseitin_0 @ (k6_relat_1 @ (k6_relat_1 @ X0)) @ X1)
% 2.15/2.36          | ((X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['45', '69'])).
% 2.15/2.36  thf('71', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         ((zip_tseitin_0 @ (k6_relat_1 @ k1_xboole_0) @ X0)
% 2.15/2.36          | ((sk_A) = (k1_relat_1 @ sk_D))
% 2.15/2.36          | ((sk_B_2) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup+', [status(thm)], ['42', '70'])).
% 2.15/2.36  thf('72', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.15/2.36      inference('simplify', [status(thm)], ['28'])).
% 2.15/2.36  thf('73', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         ((zip_tseitin_0 @ k1_xboole_0 @ X0)
% 2.15/2.36          | ((sk_A) = (k1_relat_1 @ sk_D))
% 2.15/2.36          | ((sk_B_2) = (k1_xboole_0)))),
% 2.15/2.36      inference('demod', [status(thm)], ['71', '72'])).
% 2.15/2.36  thf('74', plain, ((((sk_B_2) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf('75', plain,
% 2.15/2.36      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 2.15/2.36      inference('split', [status(esa)], ['74'])).
% 2.15/2.36  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf('77', plain,
% 2.15/2.36      ((~ (v1_funct_1 @ sk_D)
% 2.15/2.36        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 2.15/2.36        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf('78', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 2.15/2.36      inference('split', [status(esa)], ['77'])).
% 2.15/2.36  thf('79', plain, (((v1_funct_1 @ sk_D))),
% 2.15/2.36      inference('sup-', [status(thm)], ['76', '78'])).
% 2.15/2.36  thf('80', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.15/2.36      inference('demod', [status(thm)], ['61', '64'])).
% 2.15/2.36  thf('81', plain,
% 2.15/2.36      (![X51 : $i, X52 : $i, X53 : $i]:
% 2.15/2.36         (((X51) != (k1_relset_1 @ X51 @ X52 @ X53))
% 2.15/2.36          | (v1_funct_2 @ X53 @ X51 @ X52)
% 2.15/2.36          | ~ (zip_tseitin_1 @ X53 @ X52 @ X51))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.15/2.36  thf('82', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         (((X1) != (k1_xboole_0))
% 2.15/2.36          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 2.15/2.36          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['80', '81'])).
% 2.15/2.36  thf('83', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 2.15/2.36          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 2.15/2.36      inference('simplify', [status(thm)], ['82'])).
% 2.15/2.36  thf('84', plain,
% 2.15/2.36      (![X49 : $i, X50 : $i]:
% 2.15/2.36         ((zip_tseitin_0 @ X49 @ X50) | ((X50) != (k1_xboole_0)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.15/2.36  thf('85', plain, (![X49 : $i]: (zip_tseitin_0 @ X49 @ k1_xboole_0)),
% 2.15/2.36      inference('simplify', [status(thm)], ['84'])).
% 2.15/2.36  thf('86', plain,
% 2.15/2.36      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['54', '55'])).
% 2.15/2.36  thf('87', plain,
% 2.15/2.36      (![X54 : $i, X55 : $i, X56 : $i]:
% 2.15/2.36         (~ (zip_tseitin_0 @ X54 @ X55)
% 2.15/2.36          | (zip_tseitin_1 @ X56 @ X54 @ X55)
% 2.15/2.36          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54))))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.15/2.36  thf('88', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 2.15/2.36      inference('sup-', [status(thm)], ['86', '87'])).
% 2.15/2.36  thf('89', plain,
% 2.15/2.36      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.15/2.36      inference('sup-', [status(thm)], ['85', '88'])).
% 2.15/2.36  thf('90', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.15/2.36      inference('demod', [status(thm)], ['83', '89'])).
% 2.15/2.36  thf(t113_zfmisc_1, axiom,
% 2.15/2.36    (![A:$i,B:$i]:
% 2.15/2.36     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.15/2.36       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.15/2.36  thf('91', plain,
% 2.15/2.36      (![X13 : $i, X14 : $i]:
% 2.15/2.36         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 2.15/2.36          | ((X13) != (k1_xboole_0)))),
% 2.15/2.36      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.15/2.36  thf('92', plain,
% 2.15/2.36      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 2.15/2.36      inference('simplify', [status(thm)], ['91'])).
% 2.15/2.36  thf('93', plain,
% 2.15/2.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('split', [status(esa)], ['74'])).
% 2.15/2.36  thf('94', plain,
% 2.15/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.15/2.36  thf('95', plain,
% 2.15/2.36      (((m1_subset_1 @ sk_D @ 
% 2.15/2.36         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 2.15/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('sup+', [status(thm)], ['93', '94'])).
% 2.15/2.36  thf('96', plain,
% 2.15/2.36      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.15/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('sup+', [status(thm)], ['92', '95'])).
% 2.15/2.36  thf('97', plain,
% 2.15/2.36      (![X15 : $i, X16 : $i]:
% 2.15/2.36         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 2.15/2.36      inference('cnf', [status(esa)], [t3_subset])).
% 2.15/2.36  thf('98', plain,
% 2.15/2.36      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('sup-', [status(thm)], ['96', '97'])).
% 2.15/2.36  thf('99', plain,
% 2.15/2.36      (![X8 : $i, X10 : $i]:
% 2.15/2.36         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 2.15/2.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.15/2.36  thf('100', plain,
% 2.15/2.36      (((~ (r1_tarski @ k1_xboole_0 @ sk_D) | ((k1_xboole_0) = (sk_D))))
% 2.15/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('sup-', [status(thm)], ['98', '99'])).
% 2.15/2.36  thf('101', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 2.15/2.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.15/2.36  thf('102', plain,
% 2.15/2.36      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('demod', [status(thm)], ['100', '101'])).
% 2.15/2.36  thf('103', plain,
% 2.15/2.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('split', [status(esa)], ['74'])).
% 2.15/2.36  thf('104', plain,
% 2.15/2.36      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 2.15/2.36         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 2.15/2.36      inference('split', [status(esa)], ['77'])).
% 2.15/2.36  thf('105', plain,
% 2.15/2.36      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 2.15/2.36         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 2.15/2.36             (((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('sup-', [status(thm)], ['103', '104'])).
% 2.15/2.36  thf('106', plain,
% 2.15/2.36      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 2.15/2.36         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 2.15/2.36             (((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('sup-', [status(thm)], ['102', '105'])).
% 2.15/2.36  thf('107', plain,
% 2.15/2.36      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['90', '106'])).
% 2.15/2.36  thf('108', plain,
% 2.15/2.36      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.15/2.36         <= ((((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('sup+', [status(thm)], ['92', '95'])).
% 2.15/2.36  thf('109', plain,
% 2.15/2.36      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 2.15/2.36      inference('simplify', [status(thm)], ['91'])).
% 2.15/2.36  thf('110', plain,
% 2.15/2.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('split', [status(esa)], ['74'])).
% 2.15/2.36  thf('111', plain,
% 2.15/2.36      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 2.15/2.36         <= (~
% 2.15/2.36             ((m1_subset_1 @ sk_D @ 
% 2.15/2.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 2.15/2.36      inference('split', [status(esa)], ['77'])).
% 2.15/2.36  thf('112', plain,
% 2.15/2.36      ((~ (m1_subset_1 @ sk_D @ 
% 2.15/2.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 2.15/2.36         <= (~
% 2.15/2.36             ((m1_subset_1 @ sk_D @ 
% 2.15/2.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 2.15/2.36             (((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('sup-', [status(thm)], ['110', '111'])).
% 2.15/2.36  thf('113', plain,
% 2.15/2.36      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.15/2.36         <= (~
% 2.15/2.36             ((m1_subset_1 @ sk_D @ 
% 2.15/2.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 2.15/2.36             (((sk_A) = (k1_xboole_0))))),
% 2.15/2.36      inference('sup-', [status(thm)], ['109', '112'])).
% 2.15/2.36  thf('114', plain,
% 2.15/2.36      (~ (((sk_A) = (k1_xboole_0))) | 
% 2.15/2.36       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 2.15/2.36      inference('sup-', [status(thm)], ['108', '113'])).
% 2.15/2.36  thf('115', plain,
% 2.15/2.36      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 2.15/2.36       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 2.15/2.36      inference('split', [status(esa)], ['77'])).
% 2.15/2.36  thf('116', plain,
% 2.15/2.36      (~ (((sk_B_2) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 2.15/2.36      inference('split', [status(esa)], ['74'])).
% 2.15/2.36  thf('117', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 2.15/2.36      inference('sat_resolution*', [status(thm)],
% 2.15/2.36                ['79', '107', '114', '115', '116'])).
% 2.15/2.36  thf('118', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.15/2.36      inference('simpl_trail', [status(thm)], ['75', '117'])).
% 2.15/2.36  thf('119', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         ((zip_tseitin_0 @ k1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.15/2.36      inference('simplify_reflect-', [status(thm)], ['73', '118'])).
% 2.15/2.36  thf('120', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 2.15/2.36      inference('sup-', [status(thm)], ['86', '87'])).
% 2.15/2.36  thf('121', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (((sk_A) = (k1_relat_1 @ sk_D))
% 2.15/2.36          | (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['119', '120'])).
% 2.15/2.36  thf('122', plain,
% 2.15/2.36      (![X54 : $i, X55 : $i, X56 : $i]:
% 2.15/2.36         (((X54) != (k1_xboole_0))
% 2.15/2.36          | ((X55) = (k1_xboole_0))
% 2.15/2.36          | (v1_funct_2 @ X56 @ X55 @ X54)
% 2.15/2.36          | ((X56) != (k1_xboole_0))
% 2.15/2.36          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54))))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.15/2.36  thf('123', plain,
% 2.15/2.36      (![X55 : $i]:
% 2.15/2.36         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 2.15/2.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ k1_xboole_0)))
% 2.15/2.36          | (v1_funct_2 @ k1_xboole_0 @ X55 @ k1_xboole_0)
% 2.15/2.36          | ((X55) = (k1_xboole_0)))),
% 2.15/2.36      inference('simplify', [status(thm)], ['122'])).
% 2.15/2.36  thf('124', plain,
% 2.15/2.36      (![X13 : $i, X14 : $i]:
% 2.15/2.36         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 2.15/2.36          | ((X14) != (k1_xboole_0)))),
% 2.15/2.36      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.15/2.36  thf('125', plain,
% 2.15/2.36      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 2.15/2.36      inference('simplify', [status(thm)], ['124'])).
% 2.15/2.36  thf('126', plain,
% 2.15/2.36      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['54', '55'])).
% 2.15/2.36  thf('127', plain,
% 2.15/2.36      (![X55 : $i]:
% 2.15/2.36         ((v1_funct_2 @ k1_xboole_0 @ X55 @ k1_xboole_0)
% 2.15/2.36          | ((X55) = (k1_xboole_0)))),
% 2.15/2.36      inference('demod', [status(thm)], ['123', '125', '126'])).
% 2.15/2.36  thf('128', plain,
% 2.15/2.36      (![X51 : $i, X52 : $i, X53 : $i]:
% 2.15/2.36         (~ (v1_funct_2 @ X53 @ X51 @ X52)
% 2.15/2.36          | ((X51) = (k1_relset_1 @ X51 @ X52 @ X53))
% 2.15/2.36          | ~ (zip_tseitin_1 @ X53 @ X52 @ X51))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.15/2.36  thf('129', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (((X0) = (k1_xboole_0))
% 2.15/2.36          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 2.15/2.36          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['127', '128'])).
% 2.15/2.36  thf('130', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.15/2.36      inference('demod', [status(thm)], ['61', '64'])).
% 2.15/2.36  thf('131', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (((X0) = (k1_xboole_0))
% 2.15/2.36          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 2.15/2.36          | ((X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('demod', [status(thm)], ['129', '130'])).
% 2.15/2.36  thf('132', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 2.15/2.36          | ((X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('simplify', [status(thm)], ['131'])).
% 2.15/2.36  thf('133', plain,
% 2.15/2.36      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['121', '132'])).
% 2.15/2.36  thf('134', plain,
% 2.15/2.36      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['121', '132'])).
% 2.15/2.36  thf('135', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         (((X1) = (X0))
% 2.15/2.36          | ((sk_A) = (k1_relat_1 @ sk_D))
% 2.15/2.36          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.15/2.36      inference('sup+', [status(thm)], ['133', '134'])).
% 2.15/2.36  thf('136', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X1) = (X0)))),
% 2.15/2.36      inference('simplify', [status(thm)], ['135'])).
% 2.15/2.36  thf('137', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.15/2.36      inference('condensation', [status(thm)], ['136'])).
% 2.15/2.36  thf('138', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 2.15/2.36      inference('demod', [status(thm)], ['22', '137'])).
% 2.15/2.36  thf('139', plain,
% 2.15/2.36      (![X51 : $i, X52 : $i, X53 : $i]:
% 2.15/2.36         (((X51) != (k1_relset_1 @ X51 @ X52 @ X53))
% 2.15/2.36          | (v1_funct_2 @ X53 @ X51 @ X52)
% 2.15/2.36          | ~ (zip_tseitin_1 @ X53 @ X52 @ X51))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.15/2.36  thf('140', plain,
% 2.15/2.36      ((((sk_A) != (sk_A))
% 2.15/2.36        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 2.15/2.36        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 2.15/2.36      inference('sup-', [status(thm)], ['138', '139'])).
% 2.15/2.36  thf('141', plain,
% 2.15/2.36      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 2.15/2.36        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 2.15/2.36      inference('simplify', [status(thm)], ['140'])).
% 2.15/2.36  thf('142', plain,
% 2.15/2.36      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 2.15/2.36         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 2.15/2.36      inference('split', [status(esa)], ['77'])).
% 2.15/2.36  thf('143', plain,
% 2.15/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['4', '19'])).
% 2.15/2.36  thf('144', plain,
% 2.15/2.36      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 2.15/2.36         <= (~
% 2.15/2.36             ((m1_subset_1 @ sk_D @ 
% 2.15/2.36               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 2.15/2.36      inference('split', [status(esa)], ['77'])).
% 2.15/2.36  thf('145', plain,
% 2.15/2.36      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 2.15/2.36      inference('sup-', [status(thm)], ['143', '144'])).
% 2.15/2.36  thf('146', plain,
% 2.15/2.36      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 2.15/2.36       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 2.15/2.36       ~ ((v1_funct_1 @ sk_D))),
% 2.15/2.36      inference('split', [status(esa)], ['77'])).
% 2.15/2.36  thf('147', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 2.15/2.36      inference('sat_resolution*', [status(thm)], ['79', '145', '146'])).
% 2.15/2.36  thf('148', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 2.15/2.36      inference('simpl_trail', [status(thm)], ['142', '147'])).
% 2.15/2.36  thf('149', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 2.15/2.36      inference('clc', [status(thm)], ['141', '148'])).
% 2.15/2.36  thf('150', plain,
% 2.15/2.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['4', '19'])).
% 2.15/2.36  thf('151', plain,
% 2.15/2.36      (![X54 : $i, X55 : $i, X56 : $i]:
% 2.15/2.36         (~ (zip_tseitin_0 @ X54 @ X55)
% 2.15/2.36          | (zip_tseitin_1 @ X56 @ X54 @ X55)
% 2.15/2.36          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54))))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.15/2.36  thf('152', plain,
% 2.15/2.36      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 2.15/2.36        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 2.15/2.36      inference('sup-', [status(thm)], ['150', '151'])).
% 2.15/2.36  thf('153', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 2.15/2.36      inference('demod', [status(thm)], ['0', '3'])).
% 2.15/2.36  thf('154', plain,
% 2.15/2.36      (![X49 : $i, X50 : $i]:
% 2.15/2.36         ((zip_tseitin_0 @ X49 @ X50) | ((X49) = (k1_xboole_0)))),
% 2.15/2.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.15/2.36  thf('155', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 2.15/2.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.15/2.36  thf('156', plain,
% 2.15/2.36      (![X8 : $i, X10 : $i]:
% 2.15/2.36         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 2.15/2.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.15/2.36  thf('157', plain,
% 2.15/2.36      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['155', '156'])).
% 2.15/2.36  thf('158', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.15/2.36         (~ (r1_tarski @ X1 @ X0)
% 2.15/2.36          | (zip_tseitin_0 @ X0 @ X2)
% 2.15/2.36          | ((X1) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['154', '157'])).
% 2.15/2.36  thf('159', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['153', '158'])).
% 2.15/2.36  thf(fc9_relat_1, axiom,
% 2.15/2.36    (![A:$i]:
% 2.15/2.36     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 2.15/2.36       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 2.15/2.36  thf('160', plain,
% 2.15/2.36      (![X28 : $i]:
% 2.15/2.36         (~ (v1_xboole_0 @ (k2_relat_1 @ X28))
% 2.15/2.36          | ~ (v1_relat_1 @ X28)
% 2.15/2.36          | (v1_xboole_0 @ X28))),
% 2.15/2.36      inference('cnf', [status(esa)], [fc9_relat_1])).
% 2.15/2.36  thf('161', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.15/2.36          | (zip_tseitin_0 @ sk_C_1 @ X0)
% 2.15/2.36          | (v1_xboole_0 @ sk_D)
% 2.15/2.36          | ~ (v1_relat_1 @ sk_D))),
% 2.15/2.36      inference('sup-', [status(thm)], ['159', '160'])).
% 2.15/2.36  thf('162', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.15/2.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.15/2.36  thf('163', plain, ((v1_relat_1 @ sk_D)),
% 2.15/2.36      inference('demod', [status(thm)], ['12', '13'])).
% 2.15/2.36  thf('164', plain,
% 2.15/2.36      (![X0 : $i]: ((zip_tseitin_0 @ sk_C_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 2.15/2.36      inference('demod', [status(thm)], ['161', '162', '163'])).
% 2.15/2.36  thf('165', plain,
% 2.15/2.36      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['50', '51'])).
% 2.15/2.36  thf('166', plain,
% 2.15/2.36      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['50', '51'])).
% 2.15/2.36  thf('167', plain,
% 2.15/2.36      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.15/2.36      inference('demod', [status(thm)], ['83', '89'])).
% 2.15/2.36  thf('168', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.15/2.36      inference('sup+', [status(thm)], ['166', '167'])).
% 2.15/2.36  thf('169', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.15/2.36         ((v1_funct_2 @ X2 @ X0 @ X1)
% 2.15/2.36          | ~ (v1_xboole_0 @ X0)
% 2.15/2.36          | ~ (v1_xboole_0 @ X2))),
% 2.15/2.36      inference('sup+', [status(thm)], ['165', '168'])).
% 2.15/2.36  thf('170', plain,
% 2.15/2.36      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 2.15/2.36         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 2.15/2.36      inference('split', [status(esa)], ['77'])).
% 2.15/2.36  thf('171', plain,
% 2.15/2.36      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 2.15/2.36         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['169', '170'])).
% 2.15/2.36  thf('172', plain,
% 2.15/2.36      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['49', '52'])).
% 2.15/2.36  thf('173', plain,
% 2.15/2.36      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 2.15/2.36      inference('simplify', [status(thm)], ['124'])).
% 2.15/2.36  thf('174', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         (((k2_zfmisc_1 @ X1 @ (k1_relat_1 @ X0)) = (k1_xboole_0))
% 2.15/2.36          | ~ (v1_xboole_0 @ X0))),
% 2.15/2.36      inference('sup+', [status(thm)], ['172', '173'])).
% 2.15/2.36  thf('175', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 2.15/2.36      inference('simplify', [status(thm)], ['46'])).
% 2.15/2.36  thf('176', plain,
% 2.15/2.36      (![X15 : $i, X17 : $i]:
% 2.15/2.36         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 2.15/2.36      inference('cnf', [status(esa)], [t3_subset])).
% 2.15/2.36  thf('177', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['175', '176'])).
% 2.15/2.36  thf('178', plain,
% 2.15/2.36      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.15/2.36         ((v4_relat_1 @ X34 @ X35)
% 2.15/2.36          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.15/2.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.15/2.36  thf('179', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 2.15/2.36      inference('sup-', [status(thm)], ['177', '178'])).
% 2.15/2.36  thf('180', plain,
% 2.15/2.36      (![X23 : $i, X24 : $i]:
% 2.15/2.36         (~ (v4_relat_1 @ X23 @ X24)
% 2.15/2.36          | (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 2.15/2.36          | ~ (v1_relat_1 @ X23))),
% 2.15/2.36      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.15/2.36  thf('181', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 2.15/2.36          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['179', '180'])).
% 2.15/2.36  thf('182', plain,
% 2.15/2.36      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 2.15/2.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.15/2.36  thf('183', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 2.15/2.36      inference('demod', [status(thm)], ['181', '182'])).
% 2.15/2.36  thf('184', plain,
% 2.15/2.36      ((((k6_relat_1 @ sk_B_2) = (k1_xboole_0))
% 2.15/2.36        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['34', '41'])).
% 2.15/2.36  thf('185', plain, (![X30 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 2.15/2.36      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.15/2.36  thf('186', plain,
% 2.15/2.36      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['49', '52'])).
% 2.15/2.36  thf('187', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 2.15/2.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.15/2.36  thf('188', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         ((r1_tarski @ (k1_relat_1 @ X0) @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.15/2.36      inference('sup+', [status(thm)], ['186', '187'])).
% 2.15/2.36  thf('189', plain,
% 2.15/2.36      (![X0 : $i, X1 : $i]:
% 2.15/2.36         ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 2.15/2.36      inference('sup+', [status(thm)], ['185', '188'])).
% 2.15/2.36  thf('190', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.15/2.36          | ((sk_A) = (k1_relat_1 @ sk_D))
% 2.15/2.36          | (r1_tarski @ sk_B_2 @ X0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['184', '189'])).
% 2.15/2.36  thf('191', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.15/2.36      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.15/2.36  thf('192', plain,
% 2.15/2.36      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | (r1_tarski @ sk_B_2 @ X0))),
% 2.15/2.36      inference('demod', [status(thm)], ['190', '191'])).
% 2.15/2.36  thf('193', plain,
% 2.15/2.36      (![X8 : $i, X10 : $i]:
% 2.15/2.36         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 2.15/2.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.15/2.36  thf('194', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (((sk_A) = (k1_relat_1 @ sk_D))
% 2.15/2.36          | ~ (r1_tarski @ X0 @ sk_B_2)
% 2.15/2.36          | ((X0) = (sk_B_2)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['192', '193'])).
% 2.15/2.36  thf('195', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (((k1_relat_1 @ (k2_zfmisc_1 @ sk_B_2 @ X0)) = (sk_B_2))
% 2.15/2.36          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['183', '194'])).
% 2.15/2.36  thf('196', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (((k1_relat_1 @ k1_xboole_0) = (sk_B_2))
% 2.15/2.36          | ~ (v1_xboole_0 @ X0)
% 2.15/2.36          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.15/2.36      inference('sup+', [status(thm)], ['174', '195'])).
% 2.15/2.36  thf('197', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.15/2.36      inference('sup-', [status(thm)], ['62', '63'])).
% 2.15/2.36  thf('198', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         (((k1_xboole_0) = (sk_B_2))
% 2.15/2.36          | ~ (v1_xboole_0 @ X0)
% 2.15/2.36          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.15/2.36      inference('demod', [status(thm)], ['196', '197'])).
% 2.15/2.36  thf('199', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.15/2.36      inference('simpl_trail', [status(thm)], ['75', '117'])).
% 2.15/2.36  thf('200', plain,
% 2.15/2.36      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.15/2.36      inference('simplify_reflect-', [status(thm)], ['198', '199'])).
% 2.15/2.36  thf('201', plain,
% 2.15/2.36      (![X25 : $i]:
% 2.15/2.36         ((v1_xboole_0 @ (k1_relat_1 @ X25)) | ~ (v1_xboole_0 @ X25))),
% 2.15/2.36      inference('cnf', [status(esa)], [fc10_relat_1])).
% 2.15/2.36  thf('202', plain,
% 2.15/2.36      (![X0 : $i]:
% 2.15/2.36         ((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 2.15/2.36      inference('sup+', [status(thm)], ['200', '201'])).
% 2.15/2.36  thf('203', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 2.15/2.36      inference('condensation', [status(thm)], ['202'])).
% 2.15/2.36  thf('204', plain,
% 2.15/2.36      ((~ (v1_xboole_0 @ sk_D)) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 2.15/2.36      inference('clc', [status(thm)], ['171', '203'])).
% 2.15/2.36  thf('205', plain,
% 2.15/2.36      ((![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0))
% 2.15/2.36         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 2.15/2.36      inference('sup-', [status(thm)], ['164', '204'])).
% 2.15/2.36  thf('206', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 2.15/2.36      inference('sat_resolution*', [status(thm)], ['79', '145', '146'])).
% 2.15/2.36  thf('207', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 2.15/2.36      inference('simpl_trail', [status(thm)], ['205', '206'])).
% 2.15/2.36  thf('208', plain, ((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 2.15/2.36      inference('demod', [status(thm)], ['152', '207'])).
% 2.15/2.36  thf('209', plain, ($false), inference('demod', [status(thm)], ['149', '208'])).
% 2.15/2.36  
% 2.15/2.36  % SZS output end Refutation
% 2.15/2.36  
% 2.15/2.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
