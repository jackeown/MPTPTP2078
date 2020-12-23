%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9rQ9yvGXHN

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:49 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 118 expanded)
%              Number of leaves         :   38 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  597 (1411 expanded)
%              Number of equality atoms :   38 (  66 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
    | ( r2_hidden @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_D @ sk_A_1 ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('15',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('16',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1 ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_A_1
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( ( k7_partfun1 @ X30 @ X29 @ X28 )
        = ( k1_funct_1 @ X29 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A_1 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A_1 )
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
    ( ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','35'])).

thf('37',plain,(
    ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ X32 )
      | ( ( k3_funct_2 @ X32 @ X33 @ X31 @ X34 )
        = ( k1_funct_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( ( k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ( k7_partfun1 @ sk_B @ sk_C @ sk_D )
 != ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['37','47'])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9rQ9yvGXHN
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:36:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.61/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.81  % Solved by: fo/fo7.sh
% 0.61/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.81  % done 368 iterations in 0.355s
% 0.61/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.81  % SZS output start Refutation
% 0.61/0.81  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.61/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.81  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.61/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.61/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.81  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.61/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.81  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.61/0.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.61/0.81  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.81  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.61/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.61/0.81  thf(sk_D_type, type, sk_D: $i).
% 0.61/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.81  thf(t176_funct_2, conjecture,
% 0.61/0.81    (![A:$i]:
% 0.61/0.81     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.61/0.81       ( ![B:$i]:
% 0.61/0.81         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.61/0.81           ( ![C:$i]:
% 0.61/0.81             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.81                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.81               ( ![D:$i]:
% 0.61/0.81                 ( ( m1_subset_1 @ D @ A ) =>
% 0.61/0.81                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.61/0.81                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.61/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.81    (~( ![A:$i]:
% 0.61/0.81        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.61/0.81          ( ![B:$i]:
% 0.61/0.81            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.61/0.81              ( ![C:$i]:
% 0.61/0.81                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.81                    ( m1_subset_1 @
% 0.61/0.81                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.81                  ( ![D:$i]:
% 0.61/0.81                    ( ( m1_subset_1 @ D @ A ) =>
% 0.61/0.81                      ( ( k7_partfun1 @ B @ C @ D ) =
% 0.61/0.81                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.61/0.81    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 0.61/0.81  thf('0', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(cc2_relset_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.61/0.81  thf('1', plain,
% 0.61/0.81      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.61/0.81         ((v5_relat_1 @ X11 @ X13)
% 0.61/0.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.61/0.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.61/0.81  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.61/0.81      inference('sup-', [status(thm)], ['0', '1'])).
% 0.61/0.81  thf('3', plain, ((m1_subset_1 @ sk_D @ sk_A_1)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(t2_subset, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( m1_subset_1 @ A @ B ) =>
% 0.61/0.81       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.61/0.81  thf('4', plain,
% 0.61/0.81      (![X6 : $i, X7 : $i]:
% 0.61/0.81         ((r2_hidden @ X6 @ X7)
% 0.61/0.81          | (v1_xboole_0 @ X7)
% 0.61/0.81          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.61/0.81      inference('cnf', [status(esa)], [t2_subset])).
% 0.61/0.81  thf('5', plain, (((v1_xboole_0 @ sk_A_1) | (r2_hidden @ sk_D @ sk_A_1))),
% 0.61/0.81      inference('sup-', [status(thm)], ['3', '4'])).
% 0.61/0.81  thf('6', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('7', plain, ((r2_hidden @ sk_D @ sk_A_1)),
% 0.61/0.81      inference('clc', [status(thm)], ['5', '6'])).
% 0.61/0.81  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(d1_funct_2, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.81       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.81           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.61/0.81             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.61/0.81         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.81           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.61/0.81             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.61/0.81  thf(zf_stmt_1, axiom,
% 0.61/0.81    (![C:$i,B:$i,A:$i]:
% 0.61/0.81     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.61/0.81       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.61/0.81  thf('9', plain,
% 0.61/0.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.61/0.81         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.61/0.81          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.61/0.81          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.81  thf('10', plain,
% 0.61/0.81      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 0.61/0.81        | ((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B @ sk_C)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['8', '9'])).
% 0.61/0.81  thf('11', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.61/0.81  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.61/0.81  thf(zf_stmt_4, axiom,
% 0.61/0.81    (![B:$i,A:$i]:
% 0.61/0.81     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.81       ( zip_tseitin_0 @ B @ A ) ))).
% 0.61/0.81  thf(zf_stmt_5, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.81       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.61/0.81         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.81           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.61/0.81             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.61/0.81  thf('12', plain,
% 0.61/0.81      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.61/0.81         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.61/0.81          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.61/0.81          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.61/0.81  thf('13', plain,
% 0.61/0.81      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)
% 0.61/0.81        | ~ (zip_tseitin_0 @ sk_B @ sk_A_1))),
% 0.61/0.81      inference('sup-', [status(thm)], ['11', '12'])).
% 0.61/0.81  thf('14', plain,
% 0.61/0.81      (![X20 : $i, X21 : $i]:
% 0.61/0.81         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.61/0.81  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.61/0.81  thf('15', plain, ((v1_xboole_0 @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.61/0.81  thf('16', plain, ((v1_xboole_0 @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.61/0.81  thf(l13_xboole_0, axiom,
% 0.61/0.81    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.61/0.81  thf('17', plain,
% 0.61/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.61/0.81  thf('18', plain, (((sk_A) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.61/0.81  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.81      inference('demod', [status(thm)], ['15', '18'])).
% 0.61/0.81  thf('20', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['14', '19'])).
% 0.61/0.81  thf('21', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('22', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.61/0.81      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.81  thf('23', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A_1)),
% 0.61/0.81      inference('demod', [status(thm)], ['13', '22'])).
% 0.61/0.81  thf('24', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.81       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.81  thf('25', plain,
% 0.61/0.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.61/0.81         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.61/0.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.61/0.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.81  thf('26', plain,
% 0.61/0.81      (((k1_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.61/0.81      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.81  thf('27', plain, (((sk_A_1) = (k1_relat_1 @ sk_C))),
% 0.61/0.81      inference('demod', [status(thm)], ['10', '23', '26'])).
% 0.61/0.81  thf(d8_partfun1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.61/0.81       ( ![C:$i]:
% 0.61/0.81         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.61/0.81           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.61/0.81  thf('28', plain,
% 0.61/0.81      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 0.61/0.81          | ((k7_partfun1 @ X30 @ X29 @ X28) = (k1_funct_1 @ X29 @ X28))
% 0.61/0.81          | ~ (v1_funct_1 @ X29)
% 0.61/0.81          | ~ (v5_relat_1 @ X29 @ X30)
% 0.61/0.81          | ~ (v1_relat_1 @ X29))),
% 0.61/0.81      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.61/0.81  thf('29', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X0 @ sk_A_1)
% 0.61/0.81          | ~ (v1_relat_1 @ sk_C)
% 0.61/0.81          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.61/0.81          | ~ (v1_funct_1 @ sk_C)
% 0.61/0.81          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['27', '28'])).
% 0.61/0.81  thf('30', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(cc1_relset_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.81       ( v1_relat_1 @ C ) ))).
% 0.61/0.81  thf('31', plain,
% 0.61/0.81      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.61/0.81         ((v1_relat_1 @ X8)
% 0.61/0.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.61/0.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.61/0.81  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.81      inference('sup-', [status(thm)], ['30', '31'])).
% 0.61/0.81  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('34', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X0 @ sk_A_1)
% 0.61/0.81          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.61/0.81          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['29', '32', '33'])).
% 0.61/0.81  thf('35', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((k7_partfun1 @ X0 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 0.61/0.81          | ~ (v5_relat_1 @ sk_C @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['7', '34'])).
% 0.61/0.81  thf('36', plain,
% 0.61/0.81      (((k7_partfun1 @ sk_B @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.61/0.81      inference('sup-', [status(thm)], ['2', '35'])).
% 0.61/0.81  thf('37', plain,
% 0.61/0.81      (((k7_partfun1 @ sk_B @ sk_C @ sk_D)
% 0.61/0.81         != (k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ sk_D))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('38', plain, ((m1_subset_1 @ sk_D @ sk_A_1)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('39', plain,
% 0.61/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(redefinition_k3_funct_2, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.61/0.81         ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.61/0.81         ( m1_subset_1 @ D @ A ) ) =>
% 0.61/0.81       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.61/0.81  thf('40', plain,
% 0.61/0.81      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.61/0.81         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.61/0.81          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.61/0.81          | ~ (v1_funct_1 @ X31)
% 0.61/0.81          | (v1_xboole_0 @ X32)
% 0.61/0.81          | ~ (m1_subset_1 @ X34 @ X32)
% 0.61/0.81          | ((k3_funct_2 @ X32 @ X33 @ X31 @ X34) = (k1_funct_1 @ X31 @ X34)))),
% 0.61/0.81      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.61/0.81  thf('41', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.61/0.81          | ~ (m1_subset_1 @ X0 @ sk_A_1)
% 0.61/0.81          | (v1_xboole_0 @ sk_A_1)
% 0.61/0.81          | ~ (v1_funct_1 @ sk_C)
% 0.61/0.81          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.61/0.81  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('44', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.61/0.81          | ~ (m1_subset_1 @ X0 @ sk_A_1)
% 0.61/0.81          | (v1_xboole_0 @ sk_A_1))),
% 0.61/0.81      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.61/0.81  thf('45', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('46', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (~ (m1_subset_1 @ X0 @ sk_A_1)
% 0.61/0.81          | ((k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ X0)
% 0.61/0.81              = (k1_funct_1 @ sk_C @ X0)))),
% 0.61/0.81      inference('clc', [status(thm)], ['44', '45'])).
% 0.61/0.81  thf('47', plain,
% 0.61/0.81      (((k3_funct_2 @ sk_A_1 @ sk_B @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.61/0.81      inference('sup-', [status(thm)], ['38', '46'])).
% 0.61/0.81  thf('48', plain,
% 0.61/0.81      (((k7_partfun1 @ sk_B @ sk_C @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))),
% 0.61/0.81      inference('demod', [status(thm)], ['37', '47'])).
% 0.61/0.81  thf('49', plain, ($false),
% 0.61/0.81      inference('simplify_reflect-', [status(thm)], ['36', '48'])).
% 0.61/0.81  
% 0.61/0.81  % SZS output end Refutation
% 0.61/0.81  
% 0.61/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
