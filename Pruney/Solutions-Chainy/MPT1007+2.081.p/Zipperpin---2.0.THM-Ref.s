%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wBlKLSACOK

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:26 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 140 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  542 (1548 expanded)
%              Number of equality atoms :   37 (  95 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('2',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('17',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X21 @ X24 ) @ X22 )
      | ( X24
       != ( k1_funct_1 @ X22 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( k1_funct_1 @ X22 @ X21 ) ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X9 ) @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wBlKLSACOK
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.72  % Solved by: fo/fo7.sh
% 0.48/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.72  % done 153 iterations in 0.228s
% 0.48/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.72  % SZS output start Refutation
% 0.48/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.48/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.48/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.48/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.48/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.48/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.48/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.48/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.48/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.48/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.48/0.72  thf(t61_funct_2, conjecture,
% 0.48/0.72    (![A:$i,B:$i,C:$i]:
% 0.48/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.48/0.72         ( m1_subset_1 @
% 0.48/0.72           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.48/0.72       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.72         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.48/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.48/0.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.48/0.72            ( m1_subset_1 @
% 0.48/0.72              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.48/0.72          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.72            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.48/0.72    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.48/0.72  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('1', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(d1_funct_2, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i]:
% 0.48/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.48/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.48/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.48/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.48/0.72  thf(zf_stmt_1, axiom,
% 0.48/0.72    (![C:$i,B:$i,A:$i]:
% 0.48/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.48/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.48/0.72  thf('2', plain,
% 0.48/0.72      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.48/0.72         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.48/0.72          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.48/0.72          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.48/0.72  thf('3', plain,
% 0.48/0.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.48/0.72        | ((k1_tarski @ sk_A)
% 0.48/0.72            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.72  thf(zf_stmt_2, axiom,
% 0.48/0.72    (![B:$i,A:$i]:
% 0.48/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.48/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.48/0.72  thf('4', plain,
% 0.48/0.72      (![X28 : $i, X29 : $i]:
% 0.48/0.72         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.72  thf('5', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_C @ 
% 0.48/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.48/0.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.48/0.72  thf(zf_stmt_5, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i]:
% 0.48/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.48/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.48/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.48/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.48/0.72  thf('6', plain,
% 0.48/0.72      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.48/0.72         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.48/0.72          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.48/0.72          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.48/0.72  thf('7', plain,
% 0.48/0.72      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.48/0.72        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.72  thf('8', plain,
% 0.48/0.72      ((((sk_B) = (k1_xboole_0))
% 0.48/0.72        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['4', '7'])).
% 0.48/0.72  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('10', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.48/0.72      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.48/0.72  thf('11', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_C @ 
% 0.48/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i]:
% 0.48/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.48/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.48/0.72  thf('12', plain,
% 0.48/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.48/0.72         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.48/0.72          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.48/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.48/0.72  thf('13', plain,
% 0.48/0.72      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.48/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.48/0.72  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.48/0.72      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.48/0.72  thf(t69_enumset1, axiom,
% 0.48/0.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.48/0.72  thf('15', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.48/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.72  thf(d2_tarski, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i]:
% 0.48/0.72     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.48/0.72       ( ![D:$i]:
% 0.48/0.72         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.48/0.72  thf('16', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.72         (((X1) != (X0))
% 0.48/0.72          | (r2_hidden @ X1 @ X2)
% 0.48/0.72          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.48/0.72      inference('cnf', [status(esa)], [d2_tarski])).
% 0.48/0.72  thf('17', plain,
% 0.48/0.72      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['16'])).
% 0.48/0.72  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.48/0.72      inference('sup+', [status(thm)], ['15', '17'])).
% 0.48/0.72  thf('19', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.48/0.72      inference('sup+', [status(thm)], ['14', '18'])).
% 0.48/0.72  thf(d4_funct_1, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.48/0.72       ( ![B:$i,C:$i]:
% 0.48/0.72         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.48/0.72             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.48/0.72               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.48/0.72           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.48/0.72             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.48/0.72               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.48/0.72  thf('20', plain,
% 0.48/0.72      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.48/0.72         (~ (r2_hidden @ X21 @ (k1_relat_1 @ X22))
% 0.48/0.72          | (r2_hidden @ (k4_tarski @ X21 @ X24) @ X22)
% 0.48/0.72          | ((X24) != (k1_funct_1 @ X22 @ X21))
% 0.48/0.72          | ~ (v1_funct_1 @ X22)
% 0.48/0.72          | ~ (v1_relat_1 @ X22))),
% 0.48/0.72      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.48/0.72  thf('21', plain,
% 0.48/0.72      (![X21 : $i, X22 : $i]:
% 0.48/0.72         (~ (v1_relat_1 @ X22)
% 0.48/0.72          | ~ (v1_funct_1 @ X22)
% 0.48/0.72          | (r2_hidden @ (k4_tarski @ X21 @ (k1_funct_1 @ X22 @ X21)) @ X22)
% 0.48/0.72          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X22)))),
% 0.48/0.72      inference('simplify', [status(thm)], ['20'])).
% 0.48/0.72  thf('22', plain,
% 0.48/0.72      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)
% 0.48/0.72        | ~ (v1_funct_1 @ sk_C)
% 0.48/0.72        | ~ (v1_relat_1 @ sk_C))),
% 0.48/0.72      inference('sup-', [status(thm)], ['19', '21'])).
% 0.48/0.72  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('24', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_C @ 
% 0.48/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(cc2_relat_1, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( v1_relat_1 @ A ) =>
% 0.48/0.72       ( ![B:$i]:
% 0.48/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.48/0.72  thf('25', plain,
% 0.48/0.72      (![X17 : $i, X18 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.48/0.72          | (v1_relat_1 @ X17)
% 0.48/0.72          | ~ (v1_relat_1 @ X18))),
% 0.48/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.48/0.72  thf('26', plain,
% 0.48/0.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.48/0.72        | (v1_relat_1 @ sk_C))),
% 0.48/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.48/0.72  thf(fc6_relat_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.48/0.72  thf('27', plain,
% 0.48/0.72      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.48/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.48/0.72  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.48/0.72      inference('demod', [status(thm)], ['26', '27'])).
% 0.48/0.72  thf('29', plain,
% 0.48/0.72      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)),
% 0.48/0.72      inference('demod', [status(thm)], ['22', '23', '28'])).
% 0.48/0.72  thf('30', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_C @ 
% 0.48/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(l3_subset_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.48/0.72  thf('31', plain,
% 0.48/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.48/0.72         (~ (r2_hidden @ X14 @ X15)
% 0.48/0.72          | (r2_hidden @ X14 @ X16)
% 0.48/0.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.48/0.72      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.48/0.72  thf('32', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.48/0.72          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.48/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.48/0.72  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.48/0.72      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.48/0.72  thf('34', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B))
% 0.48/0.72          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.48/0.72      inference('demod', [status(thm)], ['32', '33'])).
% 0.48/0.72  thf('35', plain,
% 0.48/0.72      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.48/0.72        (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.48/0.72      inference('sup-', [status(thm)], ['29', '34'])).
% 0.48/0.72  thf('36', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.48/0.72      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.48/0.72  thf(t128_zfmisc_1, axiom,
% 0.48/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.72     ( ( r2_hidden @
% 0.48/0.72         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.48/0.72       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.48/0.72  thf('37', plain,
% 0.48/0.72      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.48/0.72         ((r2_hidden @ X11 @ X12)
% 0.48/0.72          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ 
% 0.48/0.72               (k2_zfmisc_1 @ (k1_tarski @ X9) @ X12)))),
% 0.48/0.72      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.48/0.72  thf('38', plain,
% 0.48/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.72         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ 
% 0.48/0.72             (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ X0))
% 0.48/0.72          | (r2_hidden @ X1 @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.48/0.72  thf('39', plain, ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B)),
% 0.48/0.72      inference('sup-', [status(thm)], ['35', '38'])).
% 0.48/0.72  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.48/0.72  
% 0.48/0.72  % SZS output end Refutation
% 0.48/0.72  
% 0.56/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
