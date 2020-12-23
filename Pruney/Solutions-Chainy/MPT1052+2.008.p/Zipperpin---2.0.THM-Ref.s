%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7AhEZ9Q7EL

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 161 expanded)
%              Number of leaves         :   40 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  553 (1361 expanded)
%              Number of equality atoms :   31 (  70 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t169_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( ( k1_relat_1 @ C )
            = A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
         => ( ( ( k1_relat_1 @ C )
              = A )
            & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( r2_hidden @ X28 @ ( k1_funct_2 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('2',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( r2_hidden @ X28 @ ( k1_funct_2 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('21',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('23',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['12','23'])).

thf('25',plain,(
    ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('33',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('39',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('40',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r2_xboole_0 @ X3 @ X5 )
      | ( X3 = X5 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('46',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = sk_A )
    | ( r2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['12','23'])).

thf('48',plain,(
    r2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('50',plain,(
    r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['37','52'])).

thf('54',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['28','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['25','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7AhEZ9Q7EL
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 95 iterations in 0.096s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.19/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.19/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.19/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.19/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.52  thf(t169_funct_2, conjecture,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.52       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.19/0.52         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.19/0.52           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.52        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.52          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.19/0.52            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.19/0.52              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.19/0.52  thf('0', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t121_funct_2, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.19/0.52       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.52         ((v1_funct_2 @ X28 @ X29 @ X30)
% 0.19/0.52          | ~ (r2_hidden @ X28 @ (k1_funct_2 @ X29 @ X30)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.19/0.52  thf('2', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.19/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.52  thf(d1_funct_2, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.19/0.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.19/0.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_1, axiom,
% 0.19/0.52    (![C:$i,B:$i,A:$i]:
% 0.19/0.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.19/0.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.52         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.19/0.52          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.19/0.52          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.19/0.52        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.52  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.52         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.19/0.52          | ~ (r2_hidden @ X28 @ (k1_funct_2 @ X29 @ X30)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.52         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.19/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.19/0.52        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.19/0.52      inference('demod', [status(thm)], ['4', '9'])).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      ((((k1_relat_1 @ sk_C_1) != (sk_A))
% 0.19/0.52        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      ((((k1_relat_1 @ sk_C_1) != (sk_A)))
% 0.19/0.52         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.19/0.52      inference('split', [status(esa)], ['11'])).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.52  thf(cc2_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.52         ((v5_relat_1 @ X12 @ X14)
% 0.19/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.52  thf('15', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.19/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.52  thf(d19_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ B ) =>
% 0.19/0.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (![X10 : $i, X11 : $i]:
% 0.19/0.52         (~ (v5_relat_1 @ X10 @ X11)
% 0.19/0.52          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.19/0.52          | ~ (v1_relat_1 @ X10))),
% 0.19/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.52  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.19/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))
% 0.19/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.19/0.52      inference('split', [status(esa)], ['11'])).
% 0.19/0.52  thf('21', plain, (((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      (~ (((k1_relat_1 @ sk_C_1) = (sk_A))) | 
% 0.19/0.52       ~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.19/0.52      inference('split', [status(esa)], ['11'])).
% 0.19/0.52  thf('23', plain, (~ (((k1_relat_1 @ sk_C_1) = (sk_A)))),
% 0.19/0.52      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.19/0.52  thf('24', plain, (((k1_relat_1 @ sk_C_1) != (sk_A))),
% 0.19/0.52      inference('simpl_trail', [status(thm)], ['12', '23'])).
% 0.19/0.52  thf('25', plain, (~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['10', '24'])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.52  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.19/0.52  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.19/0.52  thf(zf_stmt_4, axiom,
% 0.19/0.52    (![B:$i,A:$i]:
% 0.19/0.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.52       ( zip_tseitin_0 @ B @ A ) ))).
% 0.19/0.52  thf(zf_stmt_5, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.19/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.52         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.19/0.52          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.19/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.19/0.52        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (![X18 : $i, X19 : $i]:
% 0.19/0.52         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.19/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.52  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.19/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.19/0.52  thf(fc3_funct_2, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.19/0.52       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.19/0.52  thf('32', plain,
% 0.19/0.52      (![X26 : $i, X27 : $i]:
% 0.19/0.52         ((v1_xboole_0 @ X26)
% 0.19/0.52          | ~ (v1_xboole_0 @ X27)
% 0.19/0.52          | (v1_xboole_0 @ (k1_funct_2 @ X26 @ X27)))),
% 0.19/0.52      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.19/0.52  thf('33', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d1_xboole_0, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.52  thf('35', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.52  thf('36', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['32', '35'])).
% 0.19/0.52  thf('37', plain,
% 0.19/0.52      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['31', '36'])).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.52  thf('39', plain,
% 0.19/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.52         ((v4_relat_1 @ X12 @ X13)
% 0.19/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.52  thf('40', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.19/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.52  thf(d18_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ B ) =>
% 0.19/0.52       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.52  thf('41', plain,
% 0.19/0.52      (![X8 : $i, X9 : $i]:
% 0.19/0.52         (~ (v4_relat_1 @ X8 @ X9)
% 0.19/0.52          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.19/0.52          | ~ (v1_relat_1 @ X8))),
% 0.19/0.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.52  thf('42', plain,
% 0.19/0.52      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.52  thf('43', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('44', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.19/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.19/0.52  thf(d8_xboole_0, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.19/0.52       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.19/0.52  thf('45', plain,
% 0.19/0.52      (![X3 : $i, X5 : $i]:
% 0.19/0.52         ((r2_xboole_0 @ X3 @ X5) | ((X3) = (X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.19/0.52      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.19/0.52  thf('46', plain,
% 0.19/0.52      ((((k1_relat_1 @ sk_C_1) = (sk_A))
% 0.19/0.52        | (r2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.52  thf('47', plain, (((k1_relat_1 @ sk_C_1) != (sk_A))),
% 0.19/0.52      inference('simpl_trail', [status(thm)], ['12', '23'])).
% 0.19/0.52  thf('48', plain, ((r2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.19/0.52  thf(t6_xboole_0, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.19/0.52          ( ![C:$i]:
% 0.19/0.52            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.19/0.52  thf('49', plain,
% 0.19/0.52      (![X6 : $i, X7 : $i]:
% 0.19/0.52         (~ (r2_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.19/0.52      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.19/0.52  thf('50', plain,
% 0.19/0.52      ((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_C_1)) @ sk_A)),
% 0.19/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.52  thf('51', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.52  thf('52', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.52  thf('53', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.19/0.52      inference('sup-', [status(thm)], ['37', '52'])).
% 0.19/0.52  thf('54', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.19/0.52      inference('demod', [status(thm)], ['28', '53'])).
% 0.19/0.52  thf('55', plain, ($false), inference('demod', [status(thm)], ['25', '54'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
