%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EW44s84QRb

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:28 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 127 expanded)
%              Number of leaves         :   36 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  552 (1399 expanded)
%              Number of equality atoms :   36 (  71 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( X6
       != ( k2_relat_1 @ X4 ) )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X4: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ X4 ) )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X4 ) @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
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

thf('17',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('22',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['13','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['10','29','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['7','33','34','37'])).

thf('39',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ X30 )
       != sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) )
 != sk_C_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ sk_C_1 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ( X6
       != ( k2_relat_1 @ X4 ) )
      | ( X7
        = ( k1_funct_1 @ X4 @ ( sk_D_1 @ X7 @ X4 ) ) )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('43',plain,(
    ! [X4: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ X4 ) )
      | ( X7
        = ( k1_funct_1 @ X4 @ ( sk_D_1 @ X7 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('47',plain,
    ( sk_C_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    sk_C_1 != sk_C_1 ),
    inference(demod,[status(thm)],['40','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EW44s84QRb
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:01:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 88 iterations in 0.117s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.57  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.36/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.36/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.57  thf(t17_funct_2, conjecture,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.57       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.36/0.57            ( ![E:$i]:
% 0.36/0.57              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.57          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.36/0.57               ( ![E:$i]:
% 0.36/0.57                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.36/0.57                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.57         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.36/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.36/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.57  thf('4', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.36/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.57  thf(d5_funct_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.36/0.57           ( ![C:$i]:
% 0.36/0.57             ( ( r2_hidden @ C @ B ) <=>
% 0.36/0.57               ( ?[D:$i]:
% 0.36/0.57                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.36/0.57                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.36/0.57         (((X6) != (k2_relat_1 @ X4))
% 0.36/0.57          | (r2_hidden @ (sk_D_1 @ X7 @ X4) @ (k1_relat_1 @ X4))
% 0.36/0.57          | ~ (r2_hidden @ X7 @ X6)
% 0.36/0.57          | ~ (v1_funct_1 @ X4)
% 0.36/0.57          | ~ (v1_relat_1 @ X4))),
% 0.36/0.57      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (![X4 : $i, X7 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X4)
% 0.36/0.57          | ~ (v1_funct_1 @ X4)
% 0.36/0.57          | ~ (r2_hidden @ X7 @ (k2_relat_1 @ X4))
% 0.36/0.57          | (r2_hidden @ (sk_D_1 @ X7 @ X4) @ (k1_relat_1 @ X4)))),
% 0.36/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      (((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.36/0.57        | ~ (v1_funct_1 @ sk_D_2)
% 0.36/0.57        | ~ (v1_relat_1 @ sk_D_2))),
% 0.36/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.57  thf('8', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(d1_funct_2, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_1, axiom,
% 0.36/0.57    (![C:$i,B:$i,A:$i]:
% 0.36/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.57         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.36/0.57          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.36/0.57          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.36/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.57  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.57  thf(zf_stmt_4, axiom,
% 0.36/0.57    (![B:$i,A:$i]:
% 0.36/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.57  thf(zf_stmt_5, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.57  thf('12', plain,
% 0.36/0.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.57         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.36/0.57          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.36/0.57          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.36/0.57        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      (![X22 : $i, X23 : $i]:
% 0.36/0.57         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.57  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(cc4_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.57       ( ![C:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.57           ( v1_xboole_0 @ C ) ) ) ))).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.57         (~ (v1_xboole_0 @ X13)
% 0.36/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 0.36/0.57          | (v1_xboole_0 @ X14))),
% 0.36/0.57      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.36/0.57  thf('19', plain, (((v1_xboole_0 @ sk_D_2) | ~ (v1_xboole_0 @ sk_B))),
% 0.36/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_D_2))),
% 0.36/0.57      inference('sup-', [status(thm)], ['16', '19'])).
% 0.36/0.57  thf(fc11_relat_1, axiom,
% 0.36/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      (![X2 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X2)) | ~ (v1_xboole_0 @ X2))),
% 0.36/0.57      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      ((r2_hidden @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t7_boole, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [t7_boole])).
% 0.36/0.57  thf('24', plain, (~ (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))),
% 0.36/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.57  thf('25', plain,
% 0.36/0.57      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.36/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.57  thf('26', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_D_2))),
% 0.36/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.57  thf('27', plain, (~ (v1_xboole_0 @ sk_D_2)),
% 0.36/0.57      inference('sup-', [status(thm)], ['21', '26'])).
% 0.36/0.57  thf('28', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['20', '27'])).
% 0.36/0.57  thf('29', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)),
% 0.36/0.57      inference('demod', [status(thm)], ['13', '28'])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.57         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.36/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.36/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.57  thf('33', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.36/0.57      inference('demod', [status(thm)], ['10', '29', '32'])).
% 0.36/0.57  thf('34', plain, ((v1_funct_1 @ sk_D_2)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('35', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(cc1_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( v1_relat_1 @ C ) ))).
% 0.36/0.57  thf('36', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.57         ((v1_relat_1 @ X10)
% 0.36/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.36/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.57  thf('37', plain, ((v1_relat_1 @ sk_D_2)),
% 0.36/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.57  thf('38', plain, ((r2_hidden @ (sk_D_1 @ sk_C_1 @ sk_D_2) @ sk_A)),
% 0.36/0.57      inference('demod', [status(thm)], ['7', '33', '34', '37'])).
% 0.36/0.57  thf('39', plain,
% 0.36/0.57      (![X30 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X30 @ sk_A)
% 0.36/0.57          | ((k1_funct_1 @ sk_D_2 @ X30) != (sk_C_1)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('40', plain,
% 0.36/0.57      (((k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)) != (sk_C_1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.58  thf('41', plain, ((r2_hidden @ sk_C_1 @ (k2_relat_1 @ sk_D_2))),
% 0.36/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.36/0.58         (((X6) != (k2_relat_1 @ X4))
% 0.36/0.58          | ((X7) = (k1_funct_1 @ X4 @ (sk_D_1 @ X7 @ X4)))
% 0.36/0.58          | ~ (r2_hidden @ X7 @ X6)
% 0.36/0.58          | ~ (v1_funct_1 @ X4)
% 0.36/0.58          | ~ (v1_relat_1 @ X4))),
% 0.36/0.58      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      (![X4 : $i, X7 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X4)
% 0.36/0.58          | ~ (v1_funct_1 @ X4)
% 0.36/0.58          | ~ (r2_hidden @ X7 @ (k2_relat_1 @ X4))
% 0.36/0.58          | ((X7) = (k1_funct_1 @ X4 @ (sk_D_1 @ X7 @ X4))))),
% 0.36/0.58      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      ((((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))
% 0.36/0.58        | ~ (v1_funct_1 @ sk_D_2)
% 0.36/0.58        | ~ (v1_relat_1 @ sk_D_2))),
% 0.36/0.58      inference('sup-', [status(thm)], ['41', '43'])).
% 0.36/0.58  thf('45', plain, ((v1_funct_1 @ sk_D_2)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('46', plain, ((v1_relat_1 @ sk_D_2)),
% 0.36/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.58  thf('47', plain,
% 0.36/0.58      (((sk_C_1) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_1 @ sk_D_2)))),
% 0.36/0.58      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.58  thf('48', plain, (((sk_C_1) != (sk_C_1))),
% 0.36/0.58      inference('demod', [status(thm)], ['40', '47'])).
% 0.36/0.58  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
