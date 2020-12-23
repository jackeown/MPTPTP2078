%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2CrEqMaaou

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:46 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 102 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  540 ( 829 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X20 @ X25 )
      | ( X25
       != ( k2_enumset1 @ X24 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X20 @ ( k2_enumset1 @ X24 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X15 != X16 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X14: $i,X16: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X16 @ X17 @ X18 @ X14 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X33 ) @ X34 )
      | ~ ( r2_hidden @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( r1_tarski @ ( k2_relat_1 @ X38 ) @ ( k2_relat_1 @ X37 ) )
      | ~ ( r1_tarski @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_relat_1 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','17'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( r1_tarski @ ( k2_relat_1 @ X38 ) @ ( k2_relat_1 @ X37 ) )
      | ~ ( r1_tarski @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('25',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_relat_1 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['23','28'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('31',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2CrEqMaaou
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 356 iterations in 0.147s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.59  thf(t70_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X5 : $i, X6 : $i]:
% 0.39/0.59         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.39/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.59  thf(t71_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.59         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.39/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.39/0.59  thf(d2_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.59     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.39/0.59       ( ![F:$i]:
% 0.39/0.59         ( ( r2_hidden @ F @ E ) <=>
% 0.39/0.59           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.39/0.59                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.39/0.59  thf(zf_stmt_1, axiom,
% 0.39/0.59    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.39/0.59     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.39/0.59       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.39/0.59         ( ( F ) != ( D ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.59     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.39/0.59       ( ![F:$i]:
% 0.39/0.59         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.59         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.39/0.59          | (r2_hidden @ X20 @ X25)
% 0.39/0.59          | ((X25) != (k2_enumset1 @ X24 @ X23 @ X22 @ X21)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.59         ((r2_hidden @ X20 @ (k2_enumset1 @ X24 @ X23 @ X22 @ X21))
% 0.39/0.59          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 @ X24))),
% 0.39/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.39/0.59          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.39/0.59      inference('sup+', [status(thm)], ['1', '3'])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.59         (((X15) != (X16)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 @ X14))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X14 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.59         ~ (zip_tseitin_0 @ X16 @ X16 @ X17 @ X18 @ X14)),
% 0.39/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (r2_hidden @ X2 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.39/0.59      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['0', '7'])).
% 0.39/0.59  thf(t4_setfam_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X33 : $i, X34 : $i]:
% 0.39/0.59         ((r1_tarski @ (k1_setfam_1 @ X33) @ X34) | ~ (r2_hidden @ X34 @ X33))),
% 0.39/0.59      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.59  thf(t25_relat_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( v1_relat_1 @ B ) =>
% 0.39/0.59           ( ( r1_tarski @ A @ B ) =>
% 0.39/0.59             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.39/0.59               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X37 : $i, X38 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X37)
% 0.39/0.59          | (r1_tarski @ (k2_relat_1 @ X38) @ (k2_relat_1 @ X37))
% 0.39/0.59          | ~ (r1_tarski @ X38 @ X37)
% 0.39/0.59          | ~ (v1_relat_1 @ X38))),
% 0.39/0.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.39/0.59          | (r1_tarski @ 
% 0.39/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.39/0.59             (k2_relat_1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.59  thf(t3_subset, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X30 : $i, X32 : $i]:
% 0.39/0.59         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.39/0.59          (k1_zfmisc_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.59  thf(cc2_relat_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (![X35 : $i, X36 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.39/0.59          | (v1_relat_1 @ X35)
% 0.39/0.59          | ~ (v1_relat_1 @ X36))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (r1_tarski @ 
% 0.39/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.39/0.59             (k2_relat_1 @ X0)))),
% 0.39/0.59      inference('clc', [status(thm)], ['12', '17'])).
% 0.39/0.59  thf(t17_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.39/0.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.39/0.59  thf(t12_setfam_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X28 : $i, X29 : $i]:
% 0.39/0.59         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 0.39/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.39/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X37 : $i, X38 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X37)
% 0.39/0.59          | (r1_tarski @ (k2_relat_1 @ X38) @ (k2_relat_1 @ X37))
% 0.39/0.59          | ~ (r1_tarski @ X38 @ X37)
% 0.39/0.59          | ~ (v1_relat_1 @ X38))),
% 0.39/0.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.39/0.59          | (r1_tarski @ 
% 0.39/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.39/0.59             (k2_relat_1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.39/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X30 : $i, X32 : $i]:
% 0.39/0.59         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.39/0.59          (k1_zfmisc_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X35 : $i, X36 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.39/0.59          | (v1_relat_1 @ X35)
% 0.39/0.59          | ~ (v1_relat_1 @ X36))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (r1_tarski @ 
% 0.39/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.39/0.59             (k2_relat_1 @ X0)))),
% 0.39/0.59      inference('clc', [status(thm)], ['23', '28'])).
% 0.39/0.59  thf(t19_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.39/0.59       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.59         (~ (r1_tarski @ X2 @ X3)
% 0.39/0.59          | ~ (r1_tarski @ X2 @ X4)
% 0.39/0.59          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (![X28 : $i, X29 : $i]:
% 0.39/0.59         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 0.39/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.59         (~ (r1_tarski @ X2 @ X3)
% 0.39/0.59          | ~ (r1_tarski @ X2 @ X4)
% 0.39/0.59          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.39/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (r1_tarski @ 
% 0.39/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.39/0.59             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X2)))
% 0.39/0.59          | ~ (r1_tarski @ 
% 0.39/0.59               (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.39/0.59      inference('sup-', [status(thm)], ['29', '32'])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (r1_tarski @ 
% 0.39/0.59             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.39/0.59             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.39/0.59          | ~ (v1_relat_1 @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['18', '33'])).
% 0.39/0.59  thf(t27_relat_1, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( v1_relat_1 @ B ) =>
% 0.39/0.59           ( r1_tarski @
% 0.39/0.59             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.39/0.59             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_3, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( v1_relat_1 @ A ) =>
% 0.39/0.59          ( ![B:$i]:
% 0.39/0.59            ( ( v1_relat_1 @ B ) =>
% 0.39/0.59              ( r1_tarski @
% 0.39/0.59                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.39/0.59                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.39/0.59          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('36', plain,
% 0.39/0.59      (![X28 : $i, X29 : $i]:
% 0.39/0.59         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 0.39/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (![X28 : $i, X29 : $i]:
% 0.39/0.59         ((k1_setfam_1 @ (k2_tarski @ X28 @ X29)) = (k3_xboole_0 @ X28 @ X29))),
% 0.39/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      (~ (r1_tarski @ 
% 0.39/0.59          (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.39/0.59          (k1_setfam_1 @ 
% 0.39/0.59           (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.39/0.59      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.39/0.59  thf('39', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['34', '38'])).
% 0.39/0.59  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.60  thf('42', plain, ($false),
% 0.39/0.60      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
