%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m34w5nE7rf

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:24 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 129 expanded)
%              Number of leaves         :   40 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  550 ( 964 expanded)
%              Number of equality atoms :   34 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( r2_hidden @ X32 @ ( k1_funct_2 @ X33 @ X34 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_hidden @ X32 @ ( k1_funct_2 @ X33 @ X34 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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

thf('11',plain,(
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

thf('12',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('18',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r2_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('35',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( zip_tseitin_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','36'])).

thf('38',plain,(
    zip_tseitin_0 @ sk_B_1 @ sk_A ),
    inference(eq_fact,[status(thm)],['37'])).

thf('39',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['13','38'])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C_1 )
     != sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('51',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('53',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['42','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m34w5nE7rf
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.70  % Solved by: fo/fo7.sh
% 0.51/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.70  % done 249 iterations in 0.251s
% 0.51/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.70  % SZS output start Refutation
% 0.51/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.51/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.51/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.51/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.51/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.51/0.70  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.51/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.70  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.51/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.70  thf(t169_funct_2, conjecture,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.70       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.51/0.70         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.51/0.70           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.51/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.70        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.70          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.51/0.70            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.51/0.70              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.51/0.70    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.51/0.70  thf('0', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(t121_funct_2, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.51/0.70       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.51/0.70  thf('1', plain,
% 0.51/0.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.51/0.70         ((v1_funct_2 @ X32 @ X33 @ X34)
% 0.51/0.70          | ~ (r2_hidden @ X32 @ (k1_funct_2 @ X33 @ X34)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.51/0.70  thf('2', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.51/0.70      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.70  thf(d1_funct_2, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.51/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.51/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.51/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.51/0.70  thf(zf_stmt_1, axiom,
% 0.51/0.70    (![C:$i,B:$i,A:$i]:
% 0.51/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.51/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.51/0.70  thf('3', plain,
% 0.51/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.51/0.70         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.51/0.70          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.51/0.70          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.51/0.70  thf('4', plain,
% 0.51/0.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.51/0.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.51/0.70  thf('5', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('6', plain,
% 0.51/0.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.51/0.70         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.51/0.70          | ~ (r2_hidden @ X32 @ (k1_funct_2 @ X33 @ X34)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.51/0.70  thf('7', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.51/0.70  thf('8', plain,
% 0.51/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.70         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.51/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.51/0.70  thf('9', plain,
% 0.51/0.70      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.70  thf('10', plain,
% 0.51/0.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.51/0.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 0.51/0.70      inference('demod', [status(thm)], ['4', '9'])).
% 0.51/0.70  thf('11', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.51/0.70  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.51/0.70  thf(zf_stmt_4, axiom,
% 0.51/0.70    (![B:$i,A:$i]:
% 0.51/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.51/0.70  thf(zf_stmt_5, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.51/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.51/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.51/0.70  thf('12', plain,
% 0.51/0.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.51/0.70         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.51/0.70          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.51/0.70          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.51/0.70  thf('13', plain,
% 0.51/0.70      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 0.51/0.70        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.51/0.70  thf('14', plain,
% 0.51/0.70      (![X22 : $i, X23 : $i]:
% 0.51/0.70         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.51/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.51/0.70  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.70  thf('16', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.51/0.70      inference('sup+', [status(thm)], ['14', '15'])).
% 0.51/0.70  thf(fc3_funct_2, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.51/0.70       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.51/0.70  thf('17', plain,
% 0.51/0.70      (![X30 : $i, X31 : $i]:
% 0.51/0.70         ((v1_xboole_0 @ X30)
% 0.51/0.70          | ~ (v1_xboole_0 @ X31)
% 0.51/0.70          | (v1_xboole_0 @ (k1_funct_2 @ X30 @ X31)))),
% 0.51/0.70      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.51/0.70  thf('18', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(d1_xboole_0, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.70  thf('19', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.70  thf('20', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.51/0.70  thf('21', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['17', '20'])).
% 0.51/0.70  thf('22', plain,
% 0.51/0.70      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['16', '21'])).
% 0.51/0.70  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.70  thf(d3_tarski, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.51/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.51/0.70  thf('24', plain,
% 0.51/0.70      (![X4 : $i, X6 : $i]:
% 0.51/0.70         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.70  thf('25', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.70  thf('26', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.70  thf(d8_xboole_0, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.51/0.70       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.51/0.70  thf('27', plain,
% 0.51/0.70      (![X7 : $i, X9 : $i]:
% 0.51/0.70         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.51/0.70      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.51/0.70  thf('28', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | (r2_xboole_0 @ X1 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.51/0.70  thf('29', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.70  thf(t60_xboole_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.51/0.70  thf('30', plain,
% 0.51/0.70      (![X10 : $i, X11 : $i]:
% 0.51/0.70         (~ (r1_tarski @ X10 @ X11) | ~ (r2_xboole_0 @ X11 @ X10))),
% 0.51/0.70      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.51/0.70  thf('31', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.51/0.70  thf('32', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (((X1) = (X0)) | ~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['28', '31'])).
% 0.51/0.70  thf('33', plain,
% 0.51/0.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['23', '32'])).
% 0.51/0.70  thf('34', plain,
% 0.51/0.70      (![X22 : $i, X23 : $i]:
% 0.51/0.70         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.51/0.70  thf('35', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 0.51/0.70      inference('simplify', [status(thm)], ['34'])).
% 0.51/0.70  thf('36', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('sup+', [status(thm)], ['33', '35'])).
% 0.51/0.70  thf('37', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         ((zip_tseitin_0 @ sk_B_1 @ X1) | (zip_tseitin_0 @ X0 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['22', '36'])).
% 0.51/0.70  thf('38', plain, ((zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.51/0.70      inference('eq_fact', [status(thm)], ['37'])).
% 0.51/0.70  thf('39', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 0.51/0.70      inference('demod', [status(thm)], ['13', '38'])).
% 0.51/0.70  thf('40', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.51/0.70      inference('demod', [status(thm)], ['10', '39'])).
% 0.51/0.70  thf('41', plain,
% 0.51/0.70      ((((k1_relat_1 @ sk_C_1) != (sk_A))
% 0.51/0.70        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('42', plain,
% 0.51/0.70      ((((k1_relat_1 @ sk_C_1) != (sk_A)))
% 0.51/0.70         <= (~ (((k1_relat_1 @ sk_C_1) = (sk_A))))),
% 0.51/0.70      inference('split', [status(esa)], ['41'])).
% 0.51/0.70  thf('43', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf(cc2_relset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.51/0.70  thf('44', plain,
% 0.51/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.51/0.70         ((v5_relat_1 @ X16 @ X18)
% 0.51/0.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.70  thf('45', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.51/0.70      inference('sup-', [status(thm)], ['43', '44'])).
% 0.51/0.70  thf(d19_relat_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( v1_relat_1 @ B ) =>
% 0.51/0.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.51/0.70  thf('46', plain,
% 0.51/0.70      (![X14 : $i, X15 : $i]:
% 0.51/0.70         (~ (v5_relat_1 @ X14 @ X15)
% 0.51/0.70          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.51/0.70          | ~ (v1_relat_1 @ X14))),
% 0.51/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.51/0.70  thf('47', plain,
% 0.51/0.70      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.51/0.70  thf('48', plain, ((v1_relat_1 @ sk_C_1)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('49', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.51/0.70      inference('demod', [status(thm)], ['47', '48'])).
% 0.51/0.70  thf('50', plain,
% 0.51/0.70      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))
% 0.51/0.70         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.51/0.70      inference('split', [status(esa)], ['41'])).
% 0.51/0.70  thf('51', plain, (((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['49', '50'])).
% 0.51/0.70  thf('52', plain,
% 0.51/0.70      (~ (((k1_relat_1 @ sk_C_1) = (sk_A))) | 
% 0.51/0.70       ~ ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.51/0.70      inference('split', [status(esa)], ['41'])).
% 0.51/0.70  thf('53', plain, (~ (((k1_relat_1 @ sk_C_1) = (sk_A)))),
% 0.51/0.70      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.51/0.70  thf('54', plain, (((k1_relat_1 @ sk_C_1) != (sk_A))),
% 0.51/0.70      inference('simpl_trail', [status(thm)], ['42', '53'])).
% 0.51/0.70  thf('55', plain, ($false),
% 0.51/0.70      inference('simplify_reflect-', [status(thm)], ['40', '54'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
