%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2IKnkvqf3g

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 119 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  577 (1529 expanded)
%              Number of equality atoms :   37 ( 102 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_D @ X14 @ X12 ) @ X12 )
      | ( ( k2_relset_1 @ X13 @ X12 @ X14 )
        = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('3',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ X25 @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ X25 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ~ ( r1_tarski @ sk_B @ ( sk_D @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) )
      | ( X3
       != ( k1_funct_1 @ X2 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ X2 @ X1 ) ) @ X2 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['7','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf('37',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ X25 @ sk_B )
      | ( X25
        = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( sk_D @ sk_C @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D @ X14 @ X12 ) ) @ X14 )
      | ( ( k2_relset_1 @ X13 @ X12 @ X14 )
        = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2IKnkvqf3g
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:42:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 96 iterations in 0.102s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(t16_funct_2, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.53       ( ( ![D:$i]:
% 0.21/0.53           ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.53                ( ![E:$i]:
% 0.21/0.53                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.21/0.53                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.21/0.53         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.53            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.53          ( ( ![D:$i]:
% 0.21/0.53              ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.21/0.53                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.21/0.53            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t23_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( ![D:$i]:
% 0.21/0.53           ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.53                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.21/0.53         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_D @ X14 @ X12) @ X12)
% 0.21/0.53          | ((k2_relset_1 @ X13 @ X12 @ X14) = (X12))
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12))))),
% 0.21/0.53      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.21/0.53        | (r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X25 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X25 @ sk_B) | (r2_hidden @ (sk_E_1 @ X25) @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('7', plain, ((r2_hidden @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf(d1_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_1, axiom,
% 0.21/0.53    (![B:$i,A:$i]:
% 0.21/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.53       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.53  thf('9', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.21/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_3, axiom,
% 0.21/0.53    (![C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_5, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.53         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.21/0.53          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.21/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.53  thf('15', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.53         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.21/0.53          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.21/0.53          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.53        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.53         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.21/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '21'])).
% 0.21/0.53  thf('23', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf(t7_ordinal1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (r1_tarski @ X5 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.53  thf('25', plain, (~ (r1_tarski @ sk_B @ (sk_D @ sk_C @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.53  thf(t8_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.53         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.53           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X2))
% 0.21/0.53          | ((X3) != (k1_funct_1 @ X2 @ X1))
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ X1 @ X3) @ X2)
% 0.21/0.53          | ~ (v1_funct_1 @ X2)
% 0.21/0.53          | ~ (v1_relat_1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X2)
% 0.21/0.53          | ~ (v1_funct_1 @ X2)
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ X2 @ X1)) @ X2)
% 0.21/0.53          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X2)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C)
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.53          | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '28'])).
% 0.21/0.53  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( v1_relat_1 @ C ) ))).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.53         ((v1_relat_1 @ X6)
% 0.21/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.53  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((r2_hidden @ 
% 0.21/0.53        (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ 
% 0.21/0.53         (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)))) @ 
% 0.21/0.53        sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '34'])).
% 0.21/0.53  thf('36', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X25 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X25 @ sk_B)
% 0.21/0.53          | ((X25) = (k1_funct_1 @ sk_C @ (sk_E_1 @ X25))))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((sk_D @ sk_C @ sk_B)
% 0.21/0.53         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      ((r2_hidden @ 
% 0.21/0.53        (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ (sk_D @ sk_C @ sk_B)) @ 
% 0.21/0.53        sk_C)),
% 0.21/0.53      inference('demod', [status(thm)], ['35', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.53         (~ (r2_hidden @ (k4_tarski @ X16 @ (sk_D @ X14 @ X12)) @ X14)
% 0.21/0.53          | ((k2_relset_1 @ X13 @ X12 @ X14) = (X12))
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12))))),
% 0.21/0.53      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.21/0.53          | ((k2_relset_1 @ X0 @ sk_B @ sk_C) = (sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '41'])).
% 0.21/0.53  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('44', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
