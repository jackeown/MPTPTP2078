%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pb5d2CBp8V

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:18 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 104 expanded)
%              Number of leaves         :   42 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  549 ( 901 expanded)
%              Number of equality atoms :   38 (  54 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
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

thf('4',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_1 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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

thf('8',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_0 @ X42 @ X43 )
      | ( zip_tseitin_1 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('19',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X21 @ X20 ) @ X22 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v5_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_C @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['2','28'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['31','32'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('34',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pb5d2CBp8V
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 153 iterations in 0.117s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.57  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.40/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.40/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(t61_funct_2, conjecture,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.40/0.57         ( m1_subset_1 @
% 0.40/0.57           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.40/0.57       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.40/0.57         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.40/0.57            ( m1_subset_1 @
% 0.40/0.57              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.40/0.57          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.40/0.57            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C @ 
% 0.40/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(cc2_relset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.57  thf('1', plain,
% 0.40/0.57      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.57         ((v5_relat_1 @ X26 @ X28)
% 0.40/0.57          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.40/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.57  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.40/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.57  thf('3', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(d1_funct_2, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_1, axiom,
% 0.40/0.57    (![C:$i,B:$i,A:$i]:
% 0.40/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.40/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.57  thf('4', plain,
% 0.40/0.57      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.40/0.57         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 0.40/0.57          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 0.40/0.57          | ~ (zip_tseitin_1 @ X41 @ X40 @ X39))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.57  thf('5', plain,
% 0.40/0.57      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.40/0.57        | ((k1_tarski @ sk_A)
% 0.40/0.57            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.57  thf(zf_stmt_2, axiom,
% 0.40/0.57    (![B:$i,A:$i]:
% 0.40/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.40/0.57  thf('6', plain,
% 0.40/0.57      (![X37 : $i, X38 : $i]:
% 0.40/0.57         ((zip_tseitin_0 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.57  thf('7', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C @ 
% 0.40/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.40/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.40/0.57  thf(zf_stmt_5, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.40/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.40/0.57         (~ (zip_tseitin_0 @ X42 @ X43)
% 0.40/0.57          | (zip_tseitin_1 @ X44 @ X42 @ X43)
% 0.40/0.57          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.57  thf('9', plain,
% 0.40/0.57      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.40/0.57        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.57  thf('10', plain,
% 0.40/0.57      ((((sk_B_1) = (k1_xboole_0))
% 0.40/0.57        | (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.40/0.57  thf('11', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('12', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.40/0.57      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.40/0.57  thf('13', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C @ 
% 0.40/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.40/0.57         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.40/0.57          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.40/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.57  thf('15', plain,
% 0.40/0.57      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.40/0.57         = (k1_relat_1 @ sk_C))),
% 0.40/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.57  thf('16', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.40/0.57      inference('demod', [status(thm)], ['5', '12', '15'])).
% 0.40/0.57  thf(t69_enumset1, axiom,
% 0.40/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.57  thf('17', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.40/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.57  thf(d2_tarski, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.40/0.57       ( ![D:$i]:
% 0.40/0.57         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.40/0.57  thf('18', plain,
% 0.40/0.57      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.57         (((X4) != (X3))
% 0.40/0.57          | (r2_hidden @ X4 @ X5)
% 0.40/0.57          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d2_tarski])).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 0.40/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.57  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['17', '19'])).
% 0.40/0.57  thf('21', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.40/0.57      inference('sup+', [status(thm)], ['16', '20'])).
% 0.40/0.57  thf(t176_funct_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.57       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.40/0.57         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.40/0.57  thf('22', plain,
% 0.40/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X20 @ (k1_relat_1 @ X21))
% 0.40/0.57          | (m1_subset_1 @ (k1_funct_1 @ X21 @ X20) @ X22)
% 0.40/0.57          | ~ (v1_funct_1 @ X21)
% 0.40/0.57          | ~ (v5_relat_1 @ X21 @ X22)
% 0.40/0.57          | ~ (v1_relat_1 @ X21))),
% 0.40/0.57      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.40/0.57  thf('23', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v1_relat_1 @ sk_C)
% 0.40/0.57          | ~ (v5_relat_1 @ sk_C @ X0)
% 0.40/0.57          | ~ (v1_funct_1 @ sk_C)
% 0.40/0.57          | (m1_subset_1 @ (k1_funct_1 @ sk_C @ sk_A) @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.57  thf('24', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C @ 
% 0.40/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(cc1_relset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.57       ( v1_relat_1 @ C ) ))).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.40/0.57         ((v1_relat_1 @ X23)
% 0.40/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.40/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.57  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.57  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('28', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (v5_relat_1 @ sk_C @ X0)
% 0.40/0.57          | (m1_subset_1 @ (k1_funct_1 @ sk_C @ sk_A) @ X0))),
% 0.40/0.57      inference('demod', [status(thm)], ['23', '26', '27'])).
% 0.40/0.57  thf('29', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.40/0.57      inference('sup-', [status(thm)], ['2', '28'])).
% 0.40/0.57  thf(t2_subset, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.40/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.40/0.57  thf('30', plain,
% 0.40/0.57      (![X12 : $i, X13 : $i]:
% 0.40/0.57         ((r2_hidden @ X12 @ X13)
% 0.40/0.57          | (v1_xboole_0 @ X13)
% 0.40/0.57          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.40/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.40/0.57  thf('31', plain,
% 0.40/0.57      (((v1_xboole_0 @ sk_B_1)
% 0.40/0.57        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.57  thf('32', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('33', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.40/0.57      inference('clc', [status(thm)], ['31', '32'])).
% 0.40/0.57  thf(t34_mcart_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.57          ( ![B:$i]:
% 0.40/0.57            ( ~( ( r2_hidden @ B @ A ) & 
% 0.40/0.57                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.57                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.40/0.57                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.57  thf('34', plain,
% 0.40/0.57      (![X32 : $i]:
% 0.40/0.57         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X32) @ X32))),
% 0.40/0.57      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.40/0.57  thf(d10_xboole_0, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.57  thf('35', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.57  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.57      inference('simplify', [status(thm)], ['35'])).
% 0.40/0.57  thf(t3_subset, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.57  thf('37', plain,
% 0.40/0.57      (![X14 : $i, X16 : $i]:
% 0.40/0.57         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.57  thf('38', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.57  thf(t5_subset, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.40/0.57          ( v1_xboole_0 @ C ) ) ))).
% 0.40/0.57  thf('39', plain,
% 0.40/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X17 @ X18)
% 0.40/0.57          | ~ (v1_xboole_0 @ X19)
% 0.40/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t5_subset])).
% 0.40/0.57  thf('40', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.57  thf('41', plain,
% 0.40/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['34', '40'])).
% 0.40/0.57  thf('42', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['33', '41'])).
% 0.40/0.57  thf('43', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('44', plain, ($false),
% 0.40/0.57      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
