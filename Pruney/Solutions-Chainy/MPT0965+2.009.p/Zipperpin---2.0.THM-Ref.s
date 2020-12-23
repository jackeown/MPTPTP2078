%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zDee1Ojyie

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:58 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   74 (  92 expanded)
%              Number of leaves         :   36 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  454 ( 868 expanded)
%              Number of equality atoms :   29 (  47 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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
    v5_relat_1 @ sk_D @ sk_B_2 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
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

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','13','16'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X6 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X6 @ X5 ) @ X7 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v5_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['19','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['2','25'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(clc,[status(thm)],['28','29'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('31',plain,(
    ! [X17: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zDee1Ojyie
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:35:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 120 iterations in 0.157s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.62  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.39/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.39/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.62  thf(t7_funct_2, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ( r2_hidden @ C @ A ) =>
% 0.39/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.62           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.62            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62          ( ( r2_hidden @ C @ A ) =>
% 0.39/0.62            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.62              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(cc2_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.62         ((v5_relat_1 @ X11 @ X13)
% 0.39/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.62  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B_2)),
% 0.39/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.62  thf('3', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(d1_funct_2, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_1, axiom,
% 0.39/0.62    (![C:$i,B:$i,A:$i]:
% 0.39/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.62         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.39/0.62          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.39/0.62          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 0.39/0.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.62  thf(zf_stmt_2, axiom,
% 0.39/0.62    (![B:$i,A:$i]:
% 0.39/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X21 : $i, X22 : $i]:
% 0.39/0.62         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.62  thf(zf_stmt_5, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.62         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.39/0.62          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.39/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 0.39/0.62        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      ((((sk_B_2) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['7', '10'])).
% 0.39/0.62  thf('12', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('13', plain, ((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.62         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.39/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.62  thf('17', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.39/0.62      inference('demod', [status(thm)], ['6', '13', '16'])).
% 0.39/0.62  thf(t176_funct_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.62       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.39/0.62         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X5 @ (k1_relat_1 @ X6))
% 0.39/0.62          | (m1_subset_1 @ (k1_funct_1 @ X6 @ X5) @ X7)
% 0.39/0.62          | ~ (v1_funct_1 @ X6)
% 0.39/0.62          | ~ (v5_relat_1 @ X6 @ X7)
% 0.39/0.62          | ~ (v1_relat_1 @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.39/0.62          | ~ (v1_relat_1 @ sk_D)
% 0.39/0.62          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_D)
% 0.39/0.62          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(cc1_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( v1_relat_1 @ C ) ))).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.62         ((v1_relat_1 @ X8)
% 0.39/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.62  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.62  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.39/0.62          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.39/0.62          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.39/0.62      inference('demod', [status(thm)], ['19', '22', '23'])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ X0)
% 0.39/0.62          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['3', '24'])).
% 0.39/0.62  thf('26', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_2)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '25'])).
% 0.39/0.62  thf(t2_subset, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.39/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (![X3 : $i, X4 : $i]:
% 0.39/0.62         ((r2_hidden @ X3 @ X4)
% 0.39/0.62          | (v1_xboole_0 @ X4)
% 0.39/0.62          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_B_2)
% 0.39/0.62        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.62  thf('29', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_2)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('30', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.39/0.62      inference('clc', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf(t29_mcart_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.62          ( ![B:$i]:
% 0.39/0.62            ( ~( ( r2_hidden @ B @ A ) & 
% 0.39/0.62                 ( ![C:$i,D:$i,E:$i]:
% 0.39/0.62                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.39/0.62                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      (![X17 : $i]:
% 0.39/0.62         (((X17) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X17) @ X17))),
% 0.39/0.62      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.39/0.62  thf(d1_xboole_0, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.62  thf('34', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['30', '33'])).
% 0.39/0.62  thf('35', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('36', plain, ($false),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
