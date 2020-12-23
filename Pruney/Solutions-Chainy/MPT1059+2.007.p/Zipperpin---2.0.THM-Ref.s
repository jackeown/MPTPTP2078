%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u5cfneTYwk

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:49 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 119 expanded)
%              Number of leaves         :   40 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  617 (1429 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t176_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( k7_partfun1 @ B @ C @ D )
                    = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( k7_partfun1 @ B @ C @ D )
                      = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
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

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('12',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','23','26'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('28',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X37 ) )
      | ( ( k7_partfun1 @ X38 @ X37 @ X36 )
        = ( k1_funct_1 @ X37 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v5_relat_1 @ X37 @ X38 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ~ ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','34'])).

thf('36',plain,
    ( ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','35'])).

thf('37',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('40',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ X40 )
      | ( ( k3_funct_2 @ X40 @ X41 @ X39 @ X42 )
        = ( k1_funct_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['37','47'])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u5cfneTYwk
% 0.14/0.37  % Computer   : n017.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 17:44:17 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 347 iterations in 0.296s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i > $i).
% 0.59/0.77  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.77  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.59/0.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.77  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.59/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.77  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.59/0.77  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(t176_funct_2, conjecture,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.59/0.77           ( ![C:$i]:
% 0.59/0.77             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.77                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.77               ( ![D:$i]:
% 0.59/0.77                 ( ( m1_subset_1 @ D @ A ) =>
% 0.59/0.77                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.59/0.77                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i]:
% 0.59/0.77        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.77          ( ![B:$i]:
% 0.59/0.77            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.59/0.77              ( ![C:$i]:
% 0.59/0.77                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.77                    ( m1_subset_1 @
% 0.59/0.77                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.77                  ( ![D:$i]:
% 0.59/0.77                    ( ( m1_subset_1 @ D @ A ) =>
% 0.59/0.77                      ( ( k7_partfun1 @ B @ C @ D ) =
% 0.59/0.77                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(cc2_relset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.77         ((v5_relat_1 @ X18 @ X20)
% 0.59/0.77          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.77  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.59/0.77      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.77  thf('3', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t2_subset, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ A @ B ) =>
% 0.59/0.77       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i]:
% 0.59/0.77         ((r2_hidden @ X8 @ X9)
% 0.59/0.77          | (v1_xboole_0 @ X9)
% 0.59/0.77          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [t2_subset])).
% 0.59/0.77  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_D @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('7', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.59/0.77      inference('clc', [status(thm)], ['5', '6'])).
% 0.59/0.77  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(d1_funct_2, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.77           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.59/0.77             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.59/0.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.77           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.59/0.77             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_1, axiom,
% 0.59/0.77    (![C:$i,B:$i,A:$i]:
% 0.59/0.77     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.59/0.77       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.59/0.77         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.59/0.77          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.59/0.77          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.59/0.77        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.59/0.77  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.59/0.77  thf(zf_stmt_4, axiom,
% 0.59/0.77    (![B:$i,A:$i]:
% 0.59/0.77     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.77       ( zip_tseitin_0 @ B @ A ) ))).
% 0.59/0.77  thf(zf_stmt_5, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.59/0.77         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.77           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.59/0.77             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.59/0.77         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.59/0.77          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.59/0.77          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.59/0.78        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.78  thf('14', plain,
% 0.59/0.78      (![X28 : $i, X29 : $i]:
% 0.59/0.78         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.59/0.78  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.78  thf('15', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.59/0.78      inference('sup+', [status(thm)], ['14', '15'])).
% 0.59/0.78  thf(d1_xboole_0, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.78  thf('17', plain,
% 0.59/0.78      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.59/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.78  thf(t7_ordinal1, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      (![X13 : $i, X14 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.59/0.78      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.59/0.78  thf('19', plain,
% 0.59/0.78      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['16', '19'])).
% 0.59/0.78  thf('21', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('22', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.78  thf('23', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.59/0.78      inference('demod', [status(thm)], ['13', '22'])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(redefinition_k1_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.78         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.59/0.78          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.78  thf('26', plain,
% 0.59/0.78      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.59/0.78      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.78  thf('27', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.59/0.78      inference('demod', [status(thm)], ['10', '23', '26'])).
% 0.59/0.78  thf(d8_partfun1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.78       ( ![C:$i]:
% 0.59/0.78         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.59/0.78           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.59/0.78  thf('28', plain,
% 0.59/0.78      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X36 @ (k1_relat_1 @ X37))
% 0.59/0.78          | ((k7_partfun1 @ X38 @ X37 @ X36) = (k1_funct_1 @ X37 @ X36))
% 0.59/0.78          | ~ (v1_funct_1 @ X37)
% 0.59/0.78          | ~ (v5_relat_1 @ X37 @ X38)
% 0.59/0.78          | ~ (v1_relat_1 @ X37))),
% 0.59/0.78      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.78          | ~ (v1_relat_1 @ sk_C)
% 0.59/0.78          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.59/0.78          | ~ (v1_funct_1 @ sk_C)
% 0.59/0.78          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['27', '28'])).
% 0.59/0.78  thf('30', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(cc1_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( v1_relat_1 @ C ) ))).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.78         ((v1_relat_1 @ X15)
% 0.59/0.78          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.78  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.78      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.78  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('34', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.78          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.59/0.78          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.59/0.78      inference('demod', [status(thm)], ['29', '32', '33'])).
% 0.59/0.78  thf('35', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k7_partfun1 @ X0 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 0.59/0.78          | ~ (v5_relat_1 @ sk_C @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['7', '34'])).
% 0.59/0.78  thf('36', plain,
% 0.59/0.78      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.59/0.78      inference('sup-', [status(thm)], ['2', '35'])).
% 0.59/0.78  thf('37', plain,
% 0.59/0.78      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D)
% 0.59/0.78         != (k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('38', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(redefinition_k3_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.78     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.59/0.78         ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.78         ( m1_subset_1 @ D @ A ) ) =>
% 0.59/0.78       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.59/0.78  thf('40', plain,
% 0.59/0.78      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.59/0.78          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.59/0.78          | ~ (v1_funct_1 @ X39)
% 0.59/0.78          | (v1_xboole_0 @ X40)
% 0.59/0.78          | ~ (m1_subset_1 @ X42 @ X40)
% 0.59/0.78          | ((k3_funct_2 @ X40 @ X41 @ X39 @ X42) = (k1_funct_1 @ X39 @ X42)))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.59/0.78          | (v1_xboole_0 @ sk_A)
% 0.59/0.78          | ~ (v1_funct_1 @ sk_C)
% 0.59/0.78          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.78  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('44', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.59/0.78          | (v1_xboole_0 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.59/0.78  thf('45', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('46', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.59/0.78          | ((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0)
% 0.59/0.78              = (k1_funct_1 @ sk_C @ X0)))),
% 0.59/0.78      inference('clc', [status(thm)], ['44', '45'])).
% 0.59/0.78  thf('47', plain,
% 0.59/0.78      (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.59/0.78      inference('sup-', [status(thm)], ['38', '46'])).
% 0.59/0.78  thf('48', plain,
% 0.59/0.78      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))),
% 0.59/0.78      inference('demod', [status(thm)], ['37', '47'])).
% 0.59/0.78  thf('49', plain, ($false),
% 0.59/0.78      inference('simplify_reflect-', [status(thm)], ['36', '48'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
