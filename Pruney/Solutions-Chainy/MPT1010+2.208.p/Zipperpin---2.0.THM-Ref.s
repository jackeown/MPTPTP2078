%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lKsphyhmfN

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 187 expanded)
%              Number of leaves         :   41 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  732 (2384 expanded)
%              Number of equality atoms :   79 ( 200 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(d5_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( ( I != G )
              & ( I != F )
              & ( I != E )
              & ( I != D )
              & ( I != C )
              & ( I != B )
              & ( I != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [I: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( I != A )
        & ( I != B )
        & ( I != C )
        & ( I != D )
        & ( I != E )
        & ( I != F )
        & ( I != G ) ) ) )).

thf('0',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      | ( X35 = X36 )
      | ( X35 = X37 )
      | ( X35 = X38 )
      | ( X35 = X39 )
      | ( X35 = X40 )
      | ( X35 = X41 )
      | ( X35 = X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( r2_hidden @ X57 @ X58 )
      | ( X59 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X58 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X60 @ X57 ) @ X59 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X52 @ X51 )
      | ~ ( zip_tseitin_0 @ X52 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 )
      | ( X51
       != ( k5_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X52: $i] :
      ( ~ ( zip_tseitin_0 @ X52 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k5_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['8','22'])).

thf('24',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 != X31 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X31 ) )
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('29',plain,(
    ! [X31: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X31 ) )
     != ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('31',plain,(
    ! [X54: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X55 @ X56 ) )
      = ( k3_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X31: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X31 ) )
     != ( k1_tarski @ X31 ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('42',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lKsphyhmfN
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 115 iterations in 0.058s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.20/0.51                                               $i > $i > $o).
% 0.20/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(d5_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.51     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 0.20/0.51       ( ![I:$i]:
% 0.20/0.51         ( ( r2_hidden @ I @ H ) <=>
% 0.20/0.51           ( ~( ( ( I ) != ( G ) ) & ( ( I ) != ( F ) ) & ( ( I ) != ( E ) ) & 
% 0.20/0.51                ( ( I ) != ( D ) ) & ( ( I ) != ( C ) ) & ( ( I ) != ( B ) ) & 
% 0.20/0.51                ( ( I ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, axiom,
% 0.20/0.51    (![I:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.20/0.51       ( ( ( I ) != ( A ) ) & ( ( I ) != ( B ) ) & ( ( I ) != ( C ) ) & 
% 0.20/0.51         ( ( I ) != ( D ) ) & ( ( I ) != ( E ) ) & ( ( I ) != ( F ) ) & 
% 0.20/0.51         ( ( I ) != ( G ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, 
% 0.20/0.51         X42 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.20/0.51          | ((X35) = (X36))
% 0.20/0.51          | ((X35) = (X37))
% 0.20/0.51          | ((X35) = (X38))
% 0.20/0.51          | ((X35) = (X39))
% 0.20/0.51          | ((X35) = (X40))
% 0.20/0.51          | ((X35) = (X41))
% 0.20/0.51          | ((X35) = (X42)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t65_funct_2, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.51         ( m1_subset_1 @
% 0.20/0.51           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.51       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.51            ( m1_subset_1 @
% 0.20/0.51              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.51          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.20/0.51  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf(t7_funct_2, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X57 @ X58)
% 0.20/0.51          | ((X59) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_funct_1 @ X60)
% 0.20/0.51          | ~ (v1_funct_2 @ X60 @ X58 @ X59)
% 0.20/0.51          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ X60 @ X57) @ X59))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.51  thf(t70_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf(t69_enumset1, axiom,
% 0.20/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.51  thf('10', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf(t71_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.51         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.51  thf(t72_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.51           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.51  thf(t73_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.51     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.51       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.51         ((k4_enumset1 @ X13 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.20/0.51           = (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.51  thf(t74_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.51     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.51       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         ((k5_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.20/0.51           = (k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.20/0.51  thf(zf_stmt_2, type, zip_tseitin_0 :
% 0.20/0.51      $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_3, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.51     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 0.20/0.51       ( ![I:$i]:
% 0.20/0.51         ( ( r2_hidden @ I @ H ) <=>
% 0.20/0.51           ( ~( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, 
% 0.20/0.51         X51 : $i, X52 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X52 @ X51)
% 0.20/0.51          | ~ (zip_tseitin_0 @ X52 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.20/0.51          | ((X51) != (k5_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, 
% 0.20/0.51         X52 : $i]:
% 0.20/0.51         (~ (zip_tseitin_0 @ X52 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.20/0.51          | ~ (r2_hidden @ X52 @ 
% 0.20/0.51               (k5_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 @ X4))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 @ X3))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B @ 
% 0.20/0.51             sk_B @ sk_B @ sk_B @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.51        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.51  thf('26', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('27', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf(t20_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.51         ( k1_tarski @ A ) ) <=>
% 0.20/0.51       ( ( A ) != ( B ) ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X31 : $i, X32 : $i]:
% 0.20/0.51         (((X32) != (X31))
% 0.20/0.51          | ((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X31))
% 0.20/0.51              != (k1_tarski @ X32)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X31 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X31))
% 0.20/0.51           != (k1_tarski @ X31))),
% 0.20/0.51      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.51  thf('30', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf(t11_setfam_1, axiom,
% 0.20/0.51    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.51  thf('31', plain, (![X54 : $i]: ((k1_setfam_1 @ (k1_tarski @ X54)) = (X54))),
% 0.20/0.51      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf(t12_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X55 : $i, X56 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X55 @ X56)) = (k3_xboole_0 @ X55 @ X56))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.51  thf('34', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf(t100_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X31 : $i]:
% 0.20/0.51         ((k5_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X31))
% 0.20/0.51           != (k1_tarski @ X31))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '37'])).
% 0.20/0.51  thf('39', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf(t5_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.51  thf('40', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.51  thf('41', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('42', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.20/0.51  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
