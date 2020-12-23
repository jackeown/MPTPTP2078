%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OU0ghEkrg4

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:33 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   76 (  93 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  517 ( 751 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t24_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r1_orders_2 @ A @ B @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X35: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( l1_orders_2 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('7',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ X22 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = ( k4_tarski @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ( ( sk_B @ X22 )
       != ( k4_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','14'])).

thf(d4_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_orders_2 @ A )
      <=> ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X30: $i] :
      ( ~ ( v3_orders_2 @ X30 )
      | ( r1_relat_2 @ ( u1_orders_2 @ X30 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_orders_2 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_orders_2])).

thf(d1_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_relat_2 @ A @ B )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
             => ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_relat_2 @ X26 @ X27 )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X28 ) @ X26 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ X33 ) @ ( u1_orders_2 @ X32 ) )
      | ( r1_orders_2 @ X32 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OU0ghEkrg4
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 192 iterations in 0.186s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.64  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.45/0.64  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.45/0.64  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.45/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.45/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.64  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.45/0.64  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(t24_orders_2, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.64           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.64            ( l1_orders_2 @ A ) ) =>
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.64              ( r1_orders_2 @ A @ B @ B ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t24_orders_2])).
% 0.45/0.64  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t2_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.64       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         ((r2_hidden @ X16 @ X17)
% 0.45/0.64          | (v1_xboole_0 @ X17)
% 0.45/0.64          | ~ (m1_subset_1 @ X16 @ X17))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf(dt_u1_orders_2, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_orders_2 @ A ) =>
% 0.45/0.64       ( m1_subset_1 @
% 0.45/0.64         ( u1_orders_2 @ A ) @ 
% 0.45/0.64         ( k1_zfmisc_1 @
% 0.45/0.64           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X35 : $i]:
% 0.45/0.64         ((m1_subset_1 @ (u1_orders_2 @ X35) @ 
% 0.45/0.64           (k1_zfmisc_1 @ 
% 0.45/0.64            (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X35))))
% 0.45/0.64          | ~ (l1_orders_2 @ X35))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.45/0.64  thf(cc2_relat_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X18 : $i, X19 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.45/0.64          | (v1_relat_1 @ X18)
% 0.45/0.64          | ~ (v1_relat_1 @ X19))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (l1_orders_2 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ 
% 0.45/0.64               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.45/0.64          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf(d1_relat_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ A ) <=>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.64              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X22 : $i]: ((v1_relat_1 @ X22) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.45/0.64  thf(d2_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.45/0.64       ( ![D:$i]:
% 0.45/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.64           ( ?[E:$i,F:$i]:
% 0.45/0.64             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.45/0.64               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.45/0.64  thf(zf_stmt_2, axiom,
% 0.45/0.64    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.45/0.64     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.45/0.64       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.45/0.64         ( r2_hidden @ E @ A ) ) ))).
% 0.45/0.64  thf(zf_stmt_3, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.45/0.64       ( ![D:$i]:
% 0.45/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.64           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X12 @ X11)
% 0.45/0.64          | (zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 0.45/0.64             (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 0.45/0.64          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.45/0.64         ((zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 0.45/0.64           (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 0.45/0.64          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['8'])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.45/0.64          | (zip_tseitin_0 @ 
% 0.45/0.64             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.45/0.64             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.45/0.64             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '9'])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.64         (((X2) = (k4_tarski @ X0 @ X1))
% 0.45/0.64          | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 0.45/0.64          | ((sk_B @ (k2_zfmisc_1 @ X0 @ X1))
% 0.45/0.64              = (k4_tarski @ 
% 0.45/0.64                 (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ 
% 0.45/0.64                 (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X22) | ((sk_B @ X22) != (k4_tarski @ X23 @ X24)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))),
% 0.45/0.64      inference('clc', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['6', '14'])).
% 0.45/0.64  thf(d4_orders_2, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_orders_2 @ A ) =>
% 0.45/0.64       ( ( v3_orders_2 @ A ) <=>
% 0.45/0.64         ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X30 : $i]:
% 0.45/0.64         (~ (v3_orders_2 @ X30)
% 0.45/0.64          | (r1_relat_2 @ (u1_orders_2 @ X30) @ (u1_struct_0 @ X30))
% 0.45/0.64          | ~ (l1_orders_2 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_orders_2])).
% 0.45/0.64  thf(d1_relat_2, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( r1_relat_2 @ A @ B ) <=>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( r2_hidden @ C @ B ) =>
% 0.45/0.64               ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.64         (~ (r1_relat_2 @ X26 @ X27)
% 0.45/0.64          | (r2_hidden @ (k4_tarski @ X28 @ X28) @ X26)
% 0.45/0.64          | ~ (r2_hidden @ X28 @ X27)
% 0.45/0.64          | ~ (v1_relat_1 @ X26))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (l1_orders_2 @ X0)
% 0.45/0.64          | ~ (v3_orders_2 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 0.45/0.64          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.45/0.64          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (l1_orders_2 @ X0)
% 0.45/0.64          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.45/0.64          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.45/0.64          | ~ (v3_orders_2 @ X0)
% 0.45/0.64          | ~ (l1_orders_2 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['15', '18'])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (v3_orders_2 @ X0)
% 0.45/0.64          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.45/0.64          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.45/0.64          | ~ (l1_orders_2 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ~ (l1_orders_2 @ sk_A)
% 0.45/0.64        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ (u1_orders_2 @ sk_A))
% 0.45/0.64        | ~ (v3_orders_2 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '20'])).
% 0.45/0.64  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('23', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ (u1_orders_2 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.64  thf(d9_orders_2, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_orders_2 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.64               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.45/0.64                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.45/0.64          | ~ (r2_hidden @ (k4_tarski @ X31 @ X33) @ (u1_orders_2 @ X32))
% 0.45/0.64          | (r1_orders_2 @ X32 @ X31 @ X33)
% 0.45/0.64          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.45/0.64          | ~ (l1_orders_2 @ X32))),
% 0.45/0.64      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ~ (l1_orders_2 @ sk_A)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)
% 0.45/0.64        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('28', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('29', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1))),
% 0.45/0.64      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.45/0.64  thf('31', plain, (~ (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('32', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['30', '31'])).
% 0.45/0.64  thf(fc2_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.64       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (![X29 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X29))
% 0.45/0.64          | ~ (l1_struct_0 @ X29)
% 0.45/0.64          | (v2_struct_0 @ X29))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.64  thf('34', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.64  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(dt_l1_orders_2, axiom,
% 0.45/0.64    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_orders_2 @ X34))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.45/0.64  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.64  thf('38', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.64      inference('demod', [status(thm)], ['34', '37'])).
% 0.45/0.64  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
