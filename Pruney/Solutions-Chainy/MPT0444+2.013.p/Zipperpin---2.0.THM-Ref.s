%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E7r32leo8J

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:47 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 116 expanded)
%              Number of leaves         :   33 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  643 (1027 expanded)
%              Number of equality atoms :   29 (  51 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(d4_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( ( H != F )
              & ( H != E )
              & ( H != D )
              & ( H != C )
              & ( H != B )
              & ( H != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      | ( r2_hidden @ X40 @ X47 )
      | ( X47
       != ( k4_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ X40 @ ( k4_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 ) )
      | ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X33 != X34 )
      | ~ ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X32: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ~ ( zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X32 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('13',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X55 ) @ X56 )
      | ~ ( r2_hidden @ X56 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X59 )
      | ( r1_tarski @ ( k2_relat_1 @ X60 ) @ ( k2_relat_1 @ X59 ) )
      | ~ ( r1_tarski @ X60 @ X59 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X52: $i,X54: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ X58 ) )
      | ( v1_relat_1 @ X57 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','21'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X59 )
      | ( r1_tarski @ ( k2_relat_1 @ X60 ) @ ( k2_relat_1 @ X59 ) )
      | ~ ( r1_tarski @ X60 @ X59 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('29',plain,(
    ! [X52: $i,X54: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ X58 ) )
      | ( v1_relat_1 @ X57 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['27','32'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('35',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','37'])).

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

thf('39',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E7r32leo8J
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 545 iterations in 0.221s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.47/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.70  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.47/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.47/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.70  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.47/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.70  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.47/0.70  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.47/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.70  thf(t70_enumset1, axiom,
% 0.47/0.70    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.47/0.70  thf('0', plain,
% 0.47/0.70      (![X5 : $i, X6 : $i]:
% 0.47/0.70         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.47/0.70      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.47/0.70  thf(t71_enumset1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.47/0.70      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.47/0.70  thf(t72_enumset1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.70     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.47/0.70  thf('2', plain,
% 0.47/0.70      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.70         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.47/0.70           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.47/0.70      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.47/0.70  thf(t73_enumset1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.47/0.70     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.47/0.70       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.47/0.70  thf('3', plain,
% 0.47/0.70      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.70         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.47/0.70           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.47/0.70      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.47/0.70  thf(d4_enumset1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.47/0.70     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.47/0.70       ( ![H:$i]:
% 0.47/0.70         ( ( r2_hidden @ H @ G ) <=>
% 0.47/0.70           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.47/0.70                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.47/0.70  thf(zf_stmt_1, axiom,
% 0.47/0.70    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.47/0.70     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.47/0.70       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.47/0.70         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_2, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.47/0.70     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.47/0.70       ( ![H:$i]:
% 0.47/0.70         ( ( r2_hidden @ H @ G ) <=>
% 0.47/0.70           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.47/0.70  thf('4', plain,
% 0.47/0.70      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, 
% 0.47/0.70         X47 : $i]:
% 0.47/0.70         ((zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 0.47/0.70          | (r2_hidden @ X40 @ X47)
% 0.47/0.70          | ((X47) != (k4_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.47/0.70         ((r2_hidden @ X40 @ (k4_enumset1 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41))
% 0.47/0.70          | (zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 0.47/0.70      inference('simplify', [status(thm)], ['4'])).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.70         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.47/0.70          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.47/0.70      inference('sup+', [status(thm)], ['3', '5'])).
% 0.47/0.70  thf('7', plain,
% 0.47/0.70      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.70         (((X33) != (X34))
% 0.47/0.70          | ~ (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X32))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      (![X32 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.70         ~ (zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X32)),
% 0.47/0.70      inference('simplify', [status(thm)], ['7'])).
% 0.47/0.70  thf('9', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.70         (r2_hidden @ X4 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '8'])).
% 0.47/0.70  thf('10', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.70         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['2', '9'])).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['1', '10'])).
% 0.47/0.70  thf('12', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['0', '11'])).
% 0.47/0.70  thf(t4_setfam_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.47/0.70  thf('13', plain,
% 0.47/0.70      (![X55 : $i, X56 : $i]:
% 0.47/0.70         ((r1_tarski @ (k1_setfam_1 @ X55) @ X56) | ~ (r2_hidden @ X56 @ X55))),
% 0.47/0.70      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.47/0.70  thf('14', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.47/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf(t25_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( v1_relat_1 @ B ) =>
% 0.47/0.70           ( ( r1_tarski @ A @ B ) =>
% 0.47/0.70             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.47/0.70               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.47/0.70  thf('15', plain,
% 0.47/0.70      (![X59 : $i, X60 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X59)
% 0.47/0.70          | (r1_tarski @ (k2_relat_1 @ X60) @ (k2_relat_1 @ X59))
% 0.47/0.70          | ~ (r1_tarski @ X60 @ X59)
% 0.47/0.70          | ~ (v1_relat_1 @ X60))),
% 0.47/0.70      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.47/0.70  thf('16', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.47/0.70          | (r1_tarski @ 
% 0.47/0.70             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.47/0.70             (k2_relat_1 @ X0))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.70  thf('17', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.47/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf(t3_subset, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.70  thf('18', plain,
% 0.47/0.70      (![X52 : $i, X54 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X52 @ X54))),
% 0.47/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.70  thf('19', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.47/0.70          (k1_zfmisc_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.70  thf(cc2_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.70  thf('20', plain,
% 0.47/0.70      (![X57 : $i, X58 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ X58))
% 0.47/0.70          | (v1_relat_1 @ X57)
% 0.47/0.70          | ~ (v1_relat_1 @ X58))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.70  thf('21', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.70  thf('22', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (r1_tarski @ 
% 0.47/0.70             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.47/0.70             (k2_relat_1 @ X0)))),
% 0.47/0.70      inference('clc', [status(thm)], ['16', '21'])).
% 0.47/0.70  thf(t17_xboole_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.70  thf('23', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.47/0.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.47/0.70  thf(t12_setfam_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.70  thf('24', plain,
% 0.47/0.70      (![X50 : $i, X51 : $i]:
% 0.47/0.70         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 0.47/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.70  thf('25', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.47/0.70      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.70  thf('26', plain,
% 0.47/0.70      (![X59 : $i, X60 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X59)
% 0.47/0.70          | (r1_tarski @ (k2_relat_1 @ X60) @ (k2_relat_1 @ X59))
% 0.47/0.70          | ~ (r1_tarski @ X60 @ X59)
% 0.47/0.70          | ~ (v1_relat_1 @ X60))),
% 0.47/0.70      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.47/0.70  thf('27', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.47/0.70          | (r1_tarski @ 
% 0.47/0.70             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.47/0.70             (k2_relat_1 @ X0))
% 0.47/0.70          | ~ (v1_relat_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.70  thf('28', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.47/0.70      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.70  thf('29', plain,
% 0.47/0.70      (![X52 : $i, X54 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X52 @ X54))),
% 0.47/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.70  thf('30', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.47/0.70          (k1_zfmisc_1 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.70  thf('31', plain,
% 0.47/0.70      (![X57 : $i, X58 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ X58))
% 0.47/0.70          | (v1_relat_1 @ X57)
% 0.47/0.70          | ~ (v1_relat_1 @ X58))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.70  thf('32', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.47/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.70  thf('33', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (r1_tarski @ 
% 0.47/0.70             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.47/0.70             (k2_relat_1 @ X0)))),
% 0.47/0.70      inference('clc', [status(thm)], ['27', '32'])).
% 0.47/0.70  thf(t19_xboole_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.47/0.70       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.47/0.70  thf('34', plain,
% 0.47/0.70      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X2 @ X3)
% 0.47/0.70          | ~ (r1_tarski @ X2 @ X4)
% 0.47/0.70          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.47/0.70      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.47/0.70  thf('35', plain,
% 0.47/0.70      (![X50 : $i, X51 : $i]:
% 0.47/0.70         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 0.47/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.70  thf('36', plain,
% 0.47/0.70      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X2 @ X3)
% 0.47/0.70          | ~ (r1_tarski @ X2 @ X4)
% 0.47/0.70          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.47/0.70      inference('demod', [status(thm)], ['34', '35'])).
% 0.47/0.70  thf('37', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (r1_tarski @ 
% 0.47/0.70             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.47/0.70             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X2)))
% 0.47/0.70          | ~ (r1_tarski @ 
% 0.47/0.70               (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.47/0.70      inference('sup-', [status(thm)], ['33', '36'])).
% 0.47/0.70  thf('38', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | (r1_tarski @ 
% 0.47/0.70             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.47/0.70             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.47/0.70          | ~ (v1_relat_1 @ X1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['22', '37'])).
% 0.47/0.70  thf(t27_relat_1, conjecture,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( v1_relat_1 @ B ) =>
% 0.47/0.70           ( r1_tarski @
% 0.47/0.70             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.47/0.70             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_3, negated_conjecture,
% 0.47/0.70    (~( ![A:$i]:
% 0.47/0.70        ( ( v1_relat_1 @ A ) =>
% 0.47/0.70          ( ![B:$i]:
% 0.47/0.70            ( ( v1_relat_1 @ B ) =>
% 0.47/0.70              ( r1_tarski @
% 0.47/0.70                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.47/0.70                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.47/0.70  thf('39', plain,
% 0.47/0.70      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.47/0.70          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.70  thf('40', plain,
% 0.47/0.70      (![X50 : $i, X51 : $i]:
% 0.47/0.70         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 0.47/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.70  thf('41', plain,
% 0.47/0.70      (![X50 : $i, X51 : $i]:
% 0.47/0.70         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 0.47/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.70  thf('42', plain,
% 0.47/0.70      (~ (r1_tarski @ 
% 0.47/0.70          (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.47/0.70          (k1_setfam_1 @ 
% 0.47/0.70           (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.47/0.70      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.47/0.70  thf('43', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['38', '42'])).
% 0.47/0.70  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.70  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.70  thf('46', plain, ($false),
% 0.47/0.70      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
