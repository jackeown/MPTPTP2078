%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vgI9t0dWBy

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:58 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 198 expanded)
%              Number of leaves         :   40 (  78 expanded)
%              Depth                    :   14
%              Number of atoms          :  599 (2094 expanded)
%              Number of equality atoms :   25 (  97 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X17 @ X16 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('23',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','21','22'])).

thf('24',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_B @ sk_A ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_D @ sk_B_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['19','20'])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X17 @ X16 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['19','20'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['46','49'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['38','54'])).

thf('56',plain,(
    $false ),
    inference('sup-',[status(thm)],['27','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vgI9t0dWBy
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:13:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 100 iterations in 0.115s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(t7_funct_2, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57       ( ( r2_hidden @ C @ A ) =>
% 0.38/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.57           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57          ( ( r2_hidden @ C @ A ) =>
% 0.38/0.57            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.57              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.38/0.57  thf('0', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d1_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_1, axiom,
% 0.38/0.57    (![C:$i,B:$i,A:$i]:
% 0.38/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.38/0.57         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.38/0.57          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 0.38/0.57          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.38/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.57  thf(zf_stmt_2, axiom,
% 0.38/0.57    (![B:$i,A:$i]:
% 0.38/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X33 : $i, X34 : $i]:
% 0.38/0.57         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_5, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.38/0.57         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.38/0.57          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.38/0.57          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.38/0.57        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '6'])).
% 0.38/0.57  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('9', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.57         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.38/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.57      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.38/0.57  thf(d1_xboole_0, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.57  thf(t12_funct_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.57         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.38/0.57          | (r2_hidden @ (k1_funct_1 @ X17 @ X16) @ (k2_relat_1 @ X17))
% 0.38/0.57          | ~ (v1_funct_1 @ X17)
% 0.38/0.57          | ~ (v1_relat_1 @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_relat_1 @ X0)
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 0.38/0.57             (k2_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (((r2_hidden @ (k1_funct_1 @ sk_D @ (sk_B @ sk_A)) @ (k2_relat_1 @ sk_D))
% 0.38/0.57        | ~ (v1_funct_1 @ sk_D)
% 0.38/0.57        | ~ (v1_relat_1 @ sk_D)
% 0.38/0.57        | (v1_xboole_0 @ (k1_relat_1 @ sk_D)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['13', '16'])).
% 0.38/0.57  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc1_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( v1_relat_1 @ C ) ))).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         ((v1_relat_1 @ X18)
% 0.38/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.57  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('22', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.57      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (((r2_hidden @ (k1_funct_1 @ sk_D @ (sk_B @ sk_A)) @ (k2_relat_1 @ sk_D))
% 0.38/0.57        | (v1_xboole_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['17', '18', '21', '22'])).
% 0.38/0.57  thf('24', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.57  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      ((r2_hidden @ (k1_funct_1 @ sk_D @ (sk_B @ sk_A)) @ (k2_relat_1 @ sk_D))),
% 0.38/0.57      inference('clc', [status(thm)], ['23', '26'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc2_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.57         ((v5_relat_1 @ X21 @ X23)
% 0.38/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.57  thf('30', plain, ((v5_relat_1 @ sk_D @ sk_B_1)),
% 0.38/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.57  thf(d19_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ B ) =>
% 0.38/0.57       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i]:
% 0.38/0.57         (~ (v5_relat_1 @ X14 @ X15)
% 0.38/0.57          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.38/0.57          | ~ (v1_relat_1 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1)),
% 0.38/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf(t3_subset, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X5 : $i, X7 : $i]:
% 0.38/0.57         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.57  thf(t5_subset, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.57          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X11 @ X12)
% 0.38/0.57          | ~ (v1_xboole_0 @ X13)
% 0.38/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf('39', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('40', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.38/0.57      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X16 : $i, X17 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.38/0.57          | (r2_hidden @ (k1_funct_1 @ X17 @ X16) @ (k2_relat_1 @ X17))
% 0.38/0.57          | ~ (v1_funct_1 @ X17)
% 0.38/0.57          | ~ (v1_relat_1 @ X17))),
% 0.38/0.57      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.57          | ~ (v1_relat_1 @ sk_D)
% 0.38/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.38/0.57          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.57  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.57          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.38/0.57      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.38/0.57      inference('sup-', [status(thm)], ['39', '45'])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.57  thf(t4_subset, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.38/0.57       ( m1_subset_1 @ A @ C ) ))).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X8 @ X9)
% 0.38/0.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.38/0.57          | (m1_subset_1 @ X8 @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t4_subset])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.38/0.57          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.57  thf('50', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.38/0.57      inference('sup-', [status(thm)], ['46', '49'])).
% 0.38/0.57  thf(t2_subset, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.38/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i]:
% 0.38/0.57         ((r2_hidden @ X3 @ X4)
% 0.38/0.57          | (v1_xboole_0 @ X4)
% 0.38/0.57          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.57        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.57  thf('53', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('54', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.38/0.57      inference('clc', [status(thm)], ['52', '53'])).
% 0.38/0.57  thf('55', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D))),
% 0.38/0.57      inference('demod', [status(thm)], ['38', '54'])).
% 0.38/0.57  thf('56', plain, ($false), inference('sup-', [status(thm)], ['27', '55'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
