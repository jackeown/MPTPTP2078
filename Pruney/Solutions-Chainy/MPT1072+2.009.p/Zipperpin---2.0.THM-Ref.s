%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bqpCO9KGWo

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 112 expanded)
%              Number of leaves         :   36 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  570 (1382 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t189_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ B )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                 => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ A @ B )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                   => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t189_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_hidden @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ X23 )
      | ( ( k3_funct_2 @ X23 @ X24 @ X22 @ X25 )
        = ( k1_funct_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k1_funct_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['22','31','34'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X6 ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['37','42','43'])).

thf('45',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['4','14','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bqpCO9KGWo
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:38:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 76 iterations in 0.071s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.52  thf(t189_funct_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.52                     ( m1_subset_1 @
% 0.20/0.52                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52                   ( r2_hidden @
% 0.20/0.52                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.20/0.52                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.52                        ( m1_subset_1 @
% 0.20/0.52                          D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.52                      ( r2_hidden @
% 0.20/0.52                        ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.20/0.52                        ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t189_funct_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (~ (r2_hidden @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.20/0.52          (k2_relset_1 @ sk_A @ sk_B @ sk_D))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.20/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.52  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (~ (r2_hidden @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.20/0.52          (k2_relat_1 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.52  thf('5', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.52         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.52         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.52       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.52          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.20/0.52          | ~ (v1_funct_1 @ X22)
% 0.20/0.52          | (v1_xboole_0 @ X23)
% 0.20/0.52          | ~ (m1_subset_1 @ X25 @ X23)
% 0.20/0.52          | ((k3_funct_2 @ X23 @ X24 @ X22 @ X25) = (k1_funct_1 @ X22 @ X25)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.52          | (v1_xboole_0 @ sk_A)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.52          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.52          | (v1_xboole_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.52  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.52          | ((k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.20/0.52      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) = (k1_funct_1 @ sk_D @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '13'])).
% 0.20/0.52  thf('15', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t2_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ X1)
% 0.20/0.52          | (v1_xboole_0 @ X1)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.52  thf('17', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d1_funct_2, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_1, axiom,
% 0.20/0.52    (![C:$i,B:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.20/0.52          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.20/0.52          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.20/0.52        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_4, axiom,
% 0.20/0.52    (![B:$i,A:$i]:
% 0.20/0.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.52       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.52  thf(zf_stmt_5, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.52         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.20/0.52          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.20/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i]:
% 0.20/0.52         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.52  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('30', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['25', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.20/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '31', '34'])).
% 0.20/0.52  thf(t12_funct_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.52       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.52         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ X7 @ X6) @ (k2_relat_1 @ X7))
% 0.20/0.52          | ~ (v1_funct_1 @ X7)
% 0.20/0.52          | ~ (v1_relat_1 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.52          | ~ (v1_relat_1 @ sk_D)
% 0.20/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc2_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.20/0.52          | (v1_relat_1 @ X2)
% 0.20/0.52          | ~ (v1_relat_1 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf(fc6_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.52  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.52          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '42', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '44'])).
% 0.20/0.52  thf('46', plain, ($false),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '14', '45'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
