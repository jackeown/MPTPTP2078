%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ybvckKR5sp

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:52 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   73 (  93 expanded)
%              Number of leaves         :   36 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  527 (1187 expanded)
%              Number of equality atoms :   35 (  75 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t43_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ! [E: $i] :
            ( ? [F: $i] :
                ( ( E
                  = ( k1_funct_1 @ D @ F ) )
                & ( r2_hidden @ F @ C )
                & ( r2_hidden @ F @ A ) )
           => ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ! [E: $i] :
              ( ? [F: $i] :
                  ( ( E
                    = ( k1_funct_1 @ D @ F ) )
                  & ( r2_hidden @ F @ C )
                  & ( r2_hidden @ F @ A ) )
             => ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k9_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_F @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ sk_F @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
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
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_2 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_1 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_1 @ X28 @ X29 )
      | ( zip_tseitin_2 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k1_funct_1 @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('21',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ X4 @ X1 ) @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_F @ X0 )
      | ( zip_tseitin_0 @ sk_F @ ( k1_funct_1 @ sk_D_1 @ sk_F ) @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_F @ X0 )
      | ( zip_tseitin_0 @ sk_F @ sk_E_2 @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    zip_tseitin_0 @ sk_F @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference('sup-',[status(thm)],['4','25'])).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','3','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ybvckKR5sp
% 0.16/0.38  % Computer   : n002.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 13:38:07 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 83 iterations in 0.118s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.44/0.61  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.44/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.61  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.44/0.61  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.44/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.61  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.44/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.44/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(t43_funct_2, conjecture,
% 0.44/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.61       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.61         ( ![E:$i]:
% 0.44/0.61           ( ( ?[F:$i]:
% 0.44/0.61               ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & ( r2_hidden @ F @ C ) & 
% 0.44/0.61                 ( r2_hidden @ F @ A ) ) ) =>
% 0.44/0.61             ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.61            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.61          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.61            ( ![E:$i]:
% 0.44/0.61              ( ( ?[F:$i]:
% 0.44/0.61                  ( ( ( E ) = ( k1_funct_1 @ D @ F ) ) & 
% 0.44/0.61                    ( r2_hidden @ F @ C ) & ( r2_hidden @ F @ A ) ) ) =>
% 0.44/0.61                ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t43_funct_2])).
% 0.44/0.61  thf('0', plain,
% 0.44/0.61      (~ (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('1', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(redefinition_k7_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.61         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.44/0.61          | ((k7_relset_1 @ X20 @ X21 @ X19 @ X22) = (k9_relat_1 @ X19 @ X22)))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.44/0.61  thf('3', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.44/0.61           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.61  thf('4', plain, ((r2_hidden @ sk_F @ sk_C)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('5', plain, ((r2_hidden @ sk_F @ sk_A)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(d1_funct_2, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_1, axiom,
% 0.44/0.61    (![C:$i,B:$i,A:$i]:
% 0.44/0.61     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.44/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.61  thf('7', plain,
% 0.44/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.44/0.61         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.44/0.61          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.44/0.61          | ~ (zip_tseitin_2 @ X27 @ X26 @ X25))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.44/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.61  thf(zf_stmt_2, axiom,
% 0.44/0.61    (![B:$i,A:$i]:
% 0.44/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.61       ( zip_tseitin_1 @ B @ A ) ))).
% 0.44/0.61  thf('9', plain,
% 0.44/0.61      (![X23 : $i, X24 : $i]:
% 0.44/0.61         ((zip_tseitin_1 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.61  thf('10', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.44/0.61  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.44/0.61  thf(zf_stmt_5, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.44/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.61  thf('11', plain,
% 0.44/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.44/0.61         (~ (zip_tseitin_1 @ X28 @ X29)
% 0.44/0.61          | (zip_tseitin_2 @ X30 @ X28 @ X29)
% 0.44/0.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.61  thf('12', plain,
% 0.44/0.61      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.44/0.61        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.61  thf('13', plain,
% 0.44/0.61      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['9', '12'])).
% 0.44/0.61  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('15', plain, ((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)),
% 0.44/0.61      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.44/0.61  thf('16', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.61  thf('17', plain,
% 0.44/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.61         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.44/0.61          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.44/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.61  thf('18', plain,
% 0.44/0.61      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.61  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.44/0.61      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.44/0.61  thf(d12_funct_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.44/0.61       ( ![B:$i,C:$i]:
% 0.44/0.61         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.44/0.61           ( ![D:$i]:
% 0.44/0.61             ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.61               ( ?[E:$i]:
% 0.44/0.61                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.44/0.61                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_6, axiom,
% 0.44/0.61    (![E:$i,D:$i,B:$i,A:$i]:
% 0.44/0.61     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.44/0.61       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.44/0.61         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.44/0.61  thf('20', plain,
% 0.44/0.61      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.61         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.44/0.61          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X4))
% 0.44/0.61          | ~ (r2_hidden @ X1 @ X3)
% 0.44/0.61          | ((X2) != (k1_funct_1 @ X4 @ X1)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.44/0.61  thf('21', plain,
% 0.44/0.61      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X1 @ X3)
% 0.44/0.61          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X4))
% 0.44/0.61          | (zip_tseitin_0 @ X1 @ (k1_funct_1 @ X4 @ X1) @ X3 @ X4))),
% 0.44/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.44/0.61          | (zip_tseitin_0 @ X0 @ (k1_funct_1 @ sk_D_1 @ X0) @ X1 @ sk_D_1)
% 0.44/0.61          | ~ (r2_hidden @ X0 @ X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['19', '21'])).
% 0.44/0.61  thf('23', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r2_hidden @ sk_F @ X0)
% 0.44/0.61          | (zip_tseitin_0 @ sk_F @ (k1_funct_1 @ sk_D_1 @ sk_F) @ X0 @ sk_D_1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['5', '22'])).
% 0.44/0.61  thf('24', plain, (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ sk_F))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('25', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r2_hidden @ sk_F @ X0)
% 0.44/0.61          | (zip_tseitin_0 @ sk_F @ sk_E_2 @ X0 @ sk_D_1))),
% 0.44/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.44/0.61  thf('26', plain, ((zip_tseitin_0 @ sk_F @ sk_E_2 @ sk_C @ sk_D_1)),
% 0.44/0.61      inference('sup-', [status(thm)], ['4', '25'])).
% 0.44/0.61  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.44/0.61  thf(zf_stmt_8, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.61       ( ![B:$i,C:$i]:
% 0.44/0.61         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.44/0.61           ( ![D:$i]:
% 0.44/0.61             ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.61               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.44/0.61  thf('27', plain,
% 0.44/0.61      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.44/0.61         (((X9) != (k9_relat_1 @ X7 @ X6))
% 0.44/0.61          | (r2_hidden @ X11 @ X9)
% 0.44/0.61          | ~ (zip_tseitin_0 @ X12 @ X11 @ X6 @ X7)
% 0.44/0.61          | ~ (v1_funct_1 @ X7)
% 0.44/0.61          | ~ (v1_relat_1 @ X7))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      (![X6 : $i, X7 : $i, X11 : $i, X12 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ X7)
% 0.44/0.61          | ~ (v1_funct_1 @ X7)
% 0.44/0.61          | ~ (zip_tseitin_0 @ X12 @ X11 @ X6 @ X7)
% 0.44/0.61          | (r2_hidden @ X11 @ (k9_relat_1 @ X7 @ X6)))),
% 0.44/0.61      inference('simplify', [status(thm)], ['27'])).
% 0.44/0.61  thf('29', plain,
% 0.44/0.61      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))
% 0.44/0.61        | ~ (v1_funct_1 @ sk_D_1)
% 0.44/0.61        | ~ (v1_relat_1 @ sk_D_1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['26', '28'])).
% 0.44/0.61  thf('30', plain, ((v1_funct_1 @ sk_D_1)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('31', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(cc1_relset_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.61       ( v1_relat_1 @ C ) ))).
% 0.44/0.61  thf('32', plain,
% 0.44/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.61         ((v1_relat_1 @ X13)
% 0.44/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.44/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.61  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.61  thf('34', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.44/0.61      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.44/0.61  thf('35', plain, ($false),
% 0.44/0.61      inference('demod', [status(thm)], ['0', '3', '34'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
