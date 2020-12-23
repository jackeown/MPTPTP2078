%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E0xbM1qCw3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:26 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 122 expanded)
%              Number of leaves         :   35 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  603 (1555 expanded)
%              Number of equality atoms :   39 ( 104 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_D @ X16 @ X14 ) @ X14 )
      | ( ( k2_relset_1 @ X15 @ X14 @ X16 )
        = X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
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
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ X27 ) @ sk_A ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ~ ( r1_tarski @ sk_B @ ( sk_D @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','25'])).

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

thf('27',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ X8 ) @ X6 )
      | ( X8
       != ( k1_funct_1 @ X6 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( k1_funct_1 @ X6 @ X5 ) ) @ X6 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X6 ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30','35'])).

thf('37',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ) @ sk_C ),
    inference('sup-',[status(thm)],['7','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['3','4'])).

thf('39',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ sk_B )
      | ( X27
        = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_D @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ sk_C @ sk_B ) ) @ ( sk_D @ sk_C @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_D @ X16 @ X14 ) ) @ X16 )
      | ( ( k2_relset_1 @ X15 @ X14 @ X16 )
        = X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['0','43'])).

thf('45',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E0xbM1qCw3
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 250 iterations in 0.320s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.59/0.77  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.59/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.59/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.59/0.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.77  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 0.59/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.59/0.77  thf(t16_funct_2, conjecture,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.77       ( ( ![D:$i]:
% 0.59/0.77           ( ~( ( r2_hidden @ D @ B ) & 
% 0.59/0.77                ( ![E:$i]:
% 0.59/0.77                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.59/0.77                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.59/0.77         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.77        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.77            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.77          ( ( ![D:$i]:
% 0.59/0.77              ( ~( ( r2_hidden @ D @ B ) & 
% 0.59/0.77                   ( ![E:$i]:
% 0.59/0.77                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.59/0.77                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.59/0.77            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t23_relset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( ( ![D:$i]:
% 0.59/0.77           ( ~( ( r2_hidden @ D @ B ) & 
% 0.59/0.77                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.59/0.77         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.77         ((r2_hidden @ (sk_D @ X16 @ X14) @ X14)
% 0.59/0.77          | ((k2_relset_1 @ X15 @ X14 @ X16) = (X14))
% 0.59/0.77          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.59/0.77      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.59/0.77        | (r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.77  thf('4', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('5', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.59/0.77      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (![X27 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X27 @ sk_B) | (r2_hidden @ (sk_E_1 @ X27) @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('7', plain, ((r2_hidden @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ sk_A)),
% 0.59/0.77      inference('sup-', [status(thm)], ['5', '6'])).
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
% 0.59/0.77    (![B:$i,A:$i]:
% 0.59/0.77     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.77       ( zip_tseitin_0 @ B @ A ) ))).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i]:
% 0.59/0.77         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.77  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.77  thf('9', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.59/0.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.59/0.77      inference('sup+', [status(thm)], ['8', '9'])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.59/0.77  thf(zf_stmt_3, axiom,
% 0.59/0.77    (![C:$i,B:$i,A:$i]:
% 0.59/0.77     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.59/0.77       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.59/0.77  thf(zf_stmt_5, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.59/0.77         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.77           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.59/0.77             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.77         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.59/0.77          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.59/0.77          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['10', '13'])).
% 0.59/0.77  thf('15', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.77         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.59/0.77          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.59/0.77          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.59/0.77        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(redefinition_k1_relset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.77       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.77         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.59/0.77          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.59/0.77      inference('demod', [status(thm)], ['17', '20'])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['14', '21'])).
% 0.59/0.77  thf('23', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.59/0.77      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf(t7_ordinal1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.59/0.77      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.59/0.77  thf('25', plain, (~ (r1_tarski @ sk_B @ (sk_D @ sk_C @ sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.77  thf('26', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['22', '25'])).
% 0.59/0.77  thf(d4_funct_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.77       ( ![B:$i,C:$i]:
% 0.59/0.77         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.59/0.77             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.59/0.77               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.59/0.77           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.59/0.77             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.59/0.77               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.59/0.77  thf('27', plain,
% 0.59/0.77      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X5 @ (k1_relat_1 @ X6))
% 0.59/0.77          | (r2_hidden @ (k4_tarski @ X5 @ X8) @ X6)
% 0.59/0.77          | ((X8) != (k1_funct_1 @ X6 @ X5))
% 0.59/0.77          | ~ (v1_funct_1 @ X6)
% 0.59/0.77          | ~ (v1_relat_1 @ X6))),
% 0.59/0.77      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.59/0.77  thf('28', plain,
% 0.59/0.77      (![X5 : $i, X6 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X6)
% 0.59/0.77          | ~ (v1_funct_1 @ X6)
% 0.59/0.77          | (r2_hidden @ (k4_tarski @ X5 @ (k1_funct_1 @ X6 @ X5)) @ X6)
% 0.59/0.77          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X6)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['27'])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.77          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C)
% 0.59/0.77          | ~ (v1_funct_1 @ sk_C)
% 0.59/0.77          | ~ (v1_relat_1 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['26', '28'])).
% 0.59/0.77  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('31', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(cc2_relat_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      (![X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.59/0.77          | (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.77  thf('33', plain,
% 0.59/0.77      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.77  thf(fc6_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.59/0.77  thf('34', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.59/0.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.77  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['33', '34'])).
% 0.59/0.77  thf('36', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X0 @ sk_A)
% 0.59/0.77          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C @ X0)) @ sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['29', '30', '35'])).
% 0.59/0.77  thf('37', plain,
% 0.59/0.77      ((r2_hidden @ 
% 0.59/0.77        (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ 
% 0.59/0.77         (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)))) @ 
% 0.59/0.77        sk_C)),
% 0.59/0.77      inference('sup-', [status(thm)], ['7', '36'])).
% 0.59/0.77  thf('38', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B) @ sk_B)),
% 0.59/0.77      inference('simplify_reflect-', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf('39', plain,
% 0.59/0.77      (![X27 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X27 @ sk_B)
% 0.59/0.77          | ((X27) = (k1_funct_1 @ sk_C @ (sk_E_1 @ X27))))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('40', plain,
% 0.59/0.77      (((sk_D @ sk_C @ sk_B)
% 0.59/0.77         = (k1_funct_1 @ sk_C @ (sk_E_1 @ (sk_D @ sk_C @ sk_B))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.77  thf('41', plain,
% 0.59/0.77      ((r2_hidden @ 
% 0.59/0.77        (k4_tarski @ (sk_E_1 @ (sk_D @ sk_C @ sk_B)) @ (sk_D @ sk_C @ sk_B)) @ 
% 0.59/0.77        sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['37', '40'])).
% 0.59/0.77  thf('42', plain,
% 0.59/0.77      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.59/0.77         (~ (r2_hidden @ (k4_tarski @ X18 @ (sk_D @ X16 @ X14)) @ X16)
% 0.59/0.77          | ((k2_relset_1 @ X15 @ X14 @ X16) = (X14))
% 0.59/0.77          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.59/0.77      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.59/0.77  thf('43', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.59/0.77          | ((k2_relset_1 @ X0 @ sk_B @ sk_C) = (sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.77  thf('44', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.59/0.77      inference('sup-', [status(thm)], ['0', '43'])).
% 0.59/0.77  thf('45', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('46', plain, ($false),
% 0.59/0.77      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
