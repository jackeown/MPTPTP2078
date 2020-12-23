%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qau5aBESed

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:03 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   77 (  95 expanded)
%              Number of leaves         :   37 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  474 ( 888 expanded)
%              Number of equality atoms :   28 (  46 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X10 @ X9 ) @ X11 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v5_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['2','27'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(clc,[status(thm)],['30','31'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('33',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qau5aBESed
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:11:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 105 iterations in 0.145s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.60  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.37/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.37/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.60  thf(t7_funct_2, conjecture,
% 0.37/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.60       ( ( r2_hidden @ C @ A ) =>
% 0.37/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.60           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.60            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.60          ( ( r2_hidden @ C @ A ) =>
% 0.37/0.60            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.60              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(cc2_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.60         ((v5_relat_1 @ X12 @ X14)
% 0.37/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.37/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.60  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B_2)),
% 0.37/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.60  thf('3', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(d1_funct_2, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_1, axiom,
% 0.37/0.60    (![C:$i,B:$i,A:$i]:
% 0.37/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.60         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.37/0.60          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.37/0.60          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      ((~ (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 0.37/0.60        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.60  thf(zf_stmt_2, axiom,
% 0.37/0.60    (![B:$i,A:$i]:
% 0.37/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      (![X24 : $i, X25 : $i]:
% 0.37/0.60         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.60  thf('8', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.60  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.60  thf(zf_stmt_5, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.60         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.37/0.60          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.37/0.60          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)
% 0.37/0.60        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 0.37/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.60  thf('11', plain,
% 0.37/0.60      ((((sk_B_2) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A))),
% 0.37/0.60      inference('sup-', [status(thm)], ['7', '10'])).
% 0.37/0.60  thf('12', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('13', plain, ((zip_tseitin_1 @ sk_D @ sk_B_2 @ sk_A)),
% 0.37/0.60      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.37/0.60  thf('14', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.60         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.37/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.37/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.60  thf('17', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.60      inference('demod', [status(thm)], ['6', '13', '16'])).
% 0.37/0.60  thf(t176_funct_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.60       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.37/0.60         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 0.37/0.60          | (m1_subset_1 @ (k1_funct_1 @ X10 @ X9) @ X11)
% 0.37/0.60          | ~ (v1_funct_1 @ X10)
% 0.37/0.60          | ~ (v5_relat_1 @ X10 @ X11)
% 0.37/0.60          | ~ (v1_relat_1 @ X10))),
% 0.37/0.60      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.60          | ~ (v1_relat_1 @ sk_D)
% 0.37/0.60          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.37/0.60          | ~ (v1_funct_1 @ sk_D)
% 0.37/0.60          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(cc2_relat_1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ A ) =>
% 0.37/0.60       ( ![B:$i]:
% 0.37/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      (![X5 : $i, X6 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.37/0.60          | (v1_relat_1 @ X5)
% 0.37/0.60          | ~ (v1_relat_1 @ X6))),
% 0.37/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | (v1_relat_1 @ sk_D))),
% 0.37/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.60  thf(fc6_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.37/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.60  thf('24', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.60  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('26', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.60          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.37/0.60          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.37/0.60      inference('demod', [status(thm)], ['19', '24', '25'])).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ X0)
% 0.37/0.60          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['3', '26'])).
% 0.37/0.60  thf('28', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_2)),
% 0.37/0.60      inference('sup-', [status(thm)], ['2', '27'])).
% 0.37/0.60  thf(t2_subset, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.60       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (![X3 : $i, X4 : $i]:
% 0.37/0.60         ((r2_hidden @ X3 @ X4)
% 0.37/0.60          | (v1_xboole_0 @ X4)
% 0.37/0.60          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.37/0.60      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (((v1_xboole_0 @ sk_B_2)
% 0.37/0.60        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_2))),
% 0.37/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.60  thf('31', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_2)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('32', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.37/0.60      inference('clc', [status(thm)], ['30', '31'])).
% 0.37/0.60  thf(t6_mcart_1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.60          ( ![B:$i]:
% 0.37/0.60            ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.60                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.37/0.60                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.37/0.60                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.37/0.60                       ( r2_hidden @ G @ B ) ) =>
% 0.37/0.60                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.37/0.60  thf('33', plain,
% 0.37/0.60      (![X18 : $i]:
% 0.37/0.60         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X18) @ X18))),
% 0.37/0.60      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.37/0.60  thf(d1_xboole_0, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.60  thf('36', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['32', '35'])).
% 0.37/0.60  thf('37', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('38', plain, ($false),
% 0.37/0.60      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
