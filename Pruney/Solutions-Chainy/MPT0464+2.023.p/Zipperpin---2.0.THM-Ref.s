%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CC4U2UwH9u

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:11 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 115 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  697 (1088 expanded)
%              Number of equality atoms :   25 (  44 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      | ( r2_hidden @ X39 @ X45 )
      | ( X45
       != ( k3_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( r2_hidden @ X39 @ ( k3_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40 ) )
      | ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( X33 != X34 )
      | ~ ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X32: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ~ ( zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X32 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('11',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X53 ) @ X54 )
      | ~ ( r2_hidden @ X54 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X56 ) )
      | ( v1_relat_1 @ X55 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ~ ( r1_tarski @ X58 @ X57 )
      | ( r1_tarski @ ( k5_relat_1 @ X59 @ X58 ) @ ( k5_relat_1 @ X59 @ X57 ) )
      | ~ ( v1_relat_1 @ X59 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X56 ) )
      | ( v1_relat_1 @ X55 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ~ ( r1_tarski @ X58 @ X57 )
      | ( r1_tarski @ ( k5_relat_1 @ X59 @ X58 ) @ ( k5_relat_1 @ X59 @ X57 ) )
      | ~ ( v1_relat_1 @ X59 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

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
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45','46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CC4U2UwH9u
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.12/1.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.12/1.37  % Solved by: fo/fo7.sh
% 1.12/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.12/1.37  % done 1747 iterations in 0.910s
% 1.12/1.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.12/1.37  % SZS output start Refutation
% 1.12/1.37  thf(sk_B_type, type, sk_B: $i).
% 1.12/1.37  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.12/1.37  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.12/1.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.12/1.37  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.12/1.37  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 1.12/1.37  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.12/1.37  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.12/1.37  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.12/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.12/1.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.12/1.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.12/1.37  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.12/1.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.12/1.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.12/1.37  thf(sk_C_type, type, sk_C: $i).
% 1.12/1.37  thf(t70_enumset1, axiom,
% 1.12/1.37    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.12/1.37  thf('0', plain,
% 1.12/1.37      (![X5 : $i, X6 : $i]:
% 1.12/1.37         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 1.12/1.37      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.12/1.37  thf(t71_enumset1, axiom,
% 1.12/1.37    (![A:$i,B:$i,C:$i]:
% 1.12/1.37     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.12/1.37  thf('1', plain,
% 1.12/1.37      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.12/1.37         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.12/1.37      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.12/1.37  thf(t72_enumset1, axiom,
% 1.12/1.37    (![A:$i,B:$i,C:$i,D:$i]:
% 1.12/1.37     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.12/1.37  thf('2', plain,
% 1.12/1.37      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.12/1.37         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 1.12/1.37           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 1.12/1.37      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.12/1.37  thf(d3_enumset1, axiom,
% 1.12/1.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.12/1.37     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 1.12/1.37       ( ![G:$i]:
% 1.12/1.37         ( ( r2_hidden @ G @ F ) <=>
% 1.12/1.37           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 1.12/1.37                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 1.12/1.37  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 1.12/1.37  thf(zf_stmt_1, axiom,
% 1.12/1.37    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.12/1.37     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 1.12/1.37       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 1.12/1.37         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 1.12/1.37  thf(zf_stmt_2, axiom,
% 1.12/1.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.12/1.37     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 1.12/1.37       ( ![G:$i]:
% 1.12/1.37         ( ( r2_hidden @ G @ F ) <=>
% 1.12/1.37           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.12/1.37  thf('3', plain,
% 1.12/1.37      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.12/1.37         ((zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 1.12/1.37          | (r2_hidden @ X39 @ X45)
% 1.12/1.37          | ((X45) != (k3_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40)))),
% 1.12/1.37      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.12/1.37  thf('4', plain,
% 1.12/1.37      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.12/1.37         ((r2_hidden @ X39 @ (k3_enumset1 @ X44 @ X43 @ X42 @ X41 @ X40))
% 1.12/1.37          | (zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 1.12/1.37      inference('simplify', [status(thm)], ['3'])).
% 1.12/1.37  thf('5', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.12/1.37         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 1.12/1.37          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 1.12/1.37      inference('sup+', [status(thm)], ['2', '4'])).
% 1.12/1.37  thf('6', plain,
% 1.12/1.37      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.12/1.37         (((X33) != (X34))
% 1.12/1.37          | ~ (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X32))),
% 1.12/1.37      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.12/1.37  thf('7', plain,
% 1.12/1.37      (![X32 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.12/1.37         ~ (zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X32)),
% 1.12/1.37      inference('simplify', [status(thm)], ['6'])).
% 1.12/1.37  thf('8', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.12/1.37         (r2_hidden @ X3 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 1.12/1.37      inference('sup-', [status(thm)], ['5', '7'])).
% 1.12/1.37  thf('9', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.37         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.12/1.37      inference('sup+', [status(thm)], ['1', '8'])).
% 1.12/1.37  thf('10', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.12/1.37      inference('sup+', [status(thm)], ['0', '9'])).
% 1.12/1.37  thf(t4_setfam_1, axiom,
% 1.12/1.37    (![A:$i,B:$i]:
% 1.12/1.37     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 1.12/1.37  thf('11', plain,
% 1.12/1.37      (![X53 : $i, X54 : $i]:
% 1.12/1.37         ((r1_tarski @ (k1_setfam_1 @ X53) @ X54) | ~ (r2_hidden @ X54 @ X53))),
% 1.12/1.37      inference('cnf', [status(esa)], [t4_setfam_1])).
% 1.12/1.37  thf('12', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i]:
% 1.12/1.37         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 1.12/1.37      inference('sup-', [status(thm)], ['10', '11'])).
% 1.12/1.37  thf(t3_subset, axiom,
% 1.12/1.37    (![A:$i,B:$i]:
% 1.12/1.37     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.12/1.37  thf('13', plain,
% 1.12/1.37      (![X50 : $i, X52 : $i]:
% 1.12/1.37         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X50 @ X52))),
% 1.12/1.37      inference('cnf', [status(esa)], [t3_subset])).
% 1.12/1.37  thf('14', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i]:
% 1.12/1.37         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 1.12/1.37          (k1_zfmisc_1 @ X0))),
% 1.12/1.37      inference('sup-', [status(thm)], ['12', '13'])).
% 1.12/1.37  thf(cc2_relat_1, axiom,
% 1.12/1.37    (![A:$i]:
% 1.12/1.37     ( ( v1_relat_1 @ A ) =>
% 1.12/1.37       ( ![B:$i]:
% 1.12/1.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.12/1.37  thf('15', plain,
% 1.12/1.37      (![X55 : $i, X56 : $i]:
% 1.12/1.37         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X56))
% 1.12/1.37          | (v1_relat_1 @ X55)
% 1.12/1.37          | ~ (v1_relat_1 @ X56))),
% 1.12/1.37      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.12/1.37  thf('16', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X0)
% 1.12/1.37          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.12/1.37      inference('sup-', [status(thm)], ['14', '15'])).
% 1.12/1.37  thf('17', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i]:
% 1.12/1.37         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 1.12/1.37      inference('sup-', [status(thm)], ['10', '11'])).
% 1.12/1.37  thf(t48_relat_1, axiom,
% 1.12/1.37    (![A:$i]:
% 1.12/1.37     ( ( v1_relat_1 @ A ) =>
% 1.12/1.37       ( ![B:$i]:
% 1.12/1.37         ( ( v1_relat_1 @ B ) =>
% 1.12/1.37           ( ![C:$i]:
% 1.12/1.37             ( ( v1_relat_1 @ C ) =>
% 1.12/1.37               ( ( r1_tarski @ A @ B ) =>
% 1.12/1.37                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 1.12/1.37  thf('18', plain,
% 1.12/1.37      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X57)
% 1.12/1.37          | ~ (r1_tarski @ X58 @ X57)
% 1.12/1.37          | (r1_tarski @ (k5_relat_1 @ X59 @ X58) @ (k5_relat_1 @ X59 @ X57))
% 1.12/1.37          | ~ (v1_relat_1 @ X59)
% 1.12/1.37          | ~ (v1_relat_1 @ X58))),
% 1.12/1.37      inference('cnf', [status(esa)], [t48_relat_1])).
% 1.12/1.37  thf('19', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.12/1.37          | ~ (v1_relat_1 @ X2)
% 1.12/1.37          | (r1_tarski @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ X0))
% 1.12/1.37          | ~ (v1_relat_1 @ X0))),
% 1.12/1.37      inference('sup-', [status(thm)], ['17', '18'])).
% 1.12/1.37  thf('20', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X0)
% 1.12/1.37          | ~ (v1_relat_1 @ X0)
% 1.12/1.37          | (r1_tarski @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ X0))
% 1.12/1.37          | ~ (v1_relat_1 @ X2))),
% 1.12/1.37      inference('sup-', [status(thm)], ['16', '19'])).
% 1.12/1.37  thf('21', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X2)
% 1.12/1.37          | (r1_tarski @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ X0))
% 1.12/1.37          | ~ (v1_relat_1 @ X0))),
% 1.12/1.37      inference('simplify', [status(thm)], ['20'])).
% 1.12/1.37  thf(t17_xboole_1, axiom,
% 1.12/1.37    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.12/1.37  thf('22', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.12/1.37      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.12/1.37  thf(t12_setfam_1, axiom,
% 1.12/1.37    (![A:$i,B:$i]:
% 1.12/1.37     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.12/1.37  thf('23', plain,
% 1.12/1.37      (![X48 : $i, X49 : $i]:
% 1.12/1.37         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 1.12/1.37      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.12/1.37  thf('24', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i]:
% 1.12/1.37         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 1.12/1.37      inference('demod', [status(thm)], ['22', '23'])).
% 1.12/1.37  thf('25', plain,
% 1.12/1.37      (![X50 : $i, X52 : $i]:
% 1.12/1.37         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X50 @ X52))),
% 1.12/1.37      inference('cnf', [status(esa)], [t3_subset])).
% 1.12/1.37  thf('26', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i]:
% 1.12/1.37         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 1.12/1.37          (k1_zfmisc_1 @ X0))),
% 1.12/1.37      inference('sup-', [status(thm)], ['24', '25'])).
% 1.12/1.37  thf('27', plain,
% 1.12/1.37      (![X55 : $i, X56 : $i]:
% 1.12/1.37         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X56))
% 1.12/1.37          | (v1_relat_1 @ X55)
% 1.12/1.37          | ~ (v1_relat_1 @ X56))),
% 1.12/1.37      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.12/1.37  thf('28', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X0)
% 1.12/1.37          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 1.12/1.37      inference('sup-', [status(thm)], ['26', '27'])).
% 1.12/1.37  thf('29', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i]:
% 1.12/1.37         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 1.12/1.37      inference('demod', [status(thm)], ['22', '23'])).
% 1.12/1.37  thf('30', plain,
% 1.12/1.37      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X57)
% 1.12/1.37          | ~ (r1_tarski @ X58 @ X57)
% 1.12/1.37          | (r1_tarski @ (k5_relat_1 @ X59 @ X58) @ (k5_relat_1 @ X59 @ X57))
% 1.12/1.37          | ~ (v1_relat_1 @ X59)
% 1.12/1.37          | ~ (v1_relat_1 @ X58))),
% 1.12/1.37      inference('cnf', [status(esa)], [t48_relat_1])).
% 1.12/1.37  thf('31', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 1.12/1.37          | ~ (v1_relat_1 @ X2)
% 1.12/1.37          | (r1_tarski @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ X0))
% 1.12/1.37          | ~ (v1_relat_1 @ X0))),
% 1.12/1.37      inference('sup-', [status(thm)], ['29', '30'])).
% 1.12/1.37  thf('32', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X1)
% 1.12/1.37          | ~ (v1_relat_1 @ X1)
% 1.12/1.37          | (r1_tarski @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ X1))
% 1.12/1.37          | ~ (v1_relat_1 @ X2))),
% 1.12/1.37      inference('sup-', [status(thm)], ['28', '31'])).
% 1.12/1.37  thf('33', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X2)
% 1.12/1.37          | (r1_tarski @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 1.12/1.37             (k5_relat_1 @ X2 @ X1))
% 1.12/1.37          | ~ (v1_relat_1 @ X1))),
% 1.12/1.37      inference('simplify', [status(thm)], ['32'])).
% 1.12/1.37  thf(t19_xboole_1, axiom,
% 1.12/1.37    (![A:$i,B:$i,C:$i]:
% 1.12/1.37     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.12/1.37       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.12/1.37  thf('34', plain,
% 1.12/1.37      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.12/1.37         (~ (r1_tarski @ X2 @ X3)
% 1.12/1.37          | ~ (r1_tarski @ X2 @ X4)
% 1.12/1.37          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.12/1.37      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.12/1.37  thf('35', plain,
% 1.12/1.37      (![X48 : $i, X49 : $i]:
% 1.12/1.37         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 1.12/1.37      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.12/1.37  thf('36', plain,
% 1.12/1.37      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.12/1.37         (~ (r1_tarski @ X2 @ X3)
% 1.12/1.37          | ~ (r1_tarski @ X2 @ X4)
% 1.12/1.37          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 1.12/1.37      inference('demod', [status(thm)], ['34', '35'])).
% 1.12/1.37  thf('37', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X0)
% 1.12/1.37          | ~ (v1_relat_1 @ X1)
% 1.12/1.37          | (r1_tarski @ 
% 1.12/1.37             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 1.12/1.37             (k1_setfam_1 @ (k2_tarski @ (k5_relat_1 @ X1 @ X0) @ X3)))
% 1.12/1.37          | ~ (r1_tarski @ 
% 1.12/1.37               (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 1.12/1.37      inference('sup-', [status(thm)], ['33', '36'])).
% 1.12/1.37  thf('38', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X0)
% 1.12/1.37          | ~ (v1_relat_1 @ X1)
% 1.12/1.37          | (r1_tarski @ 
% 1.12/1.37             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 1.12/1.37             (k1_setfam_1 @ 
% 1.12/1.37              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 1.12/1.37          | ~ (v1_relat_1 @ X1)
% 1.12/1.37          | ~ (v1_relat_1 @ X2))),
% 1.12/1.37      inference('sup-', [status(thm)], ['21', '37'])).
% 1.12/1.37  thf('39', plain,
% 1.12/1.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.37         (~ (v1_relat_1 @ X2)
% 1.12/1.37          | (r1_tarski @ 
% 1.12/1.37             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 1.12/1.37             (k1_setfam_1 @ 
% 1.12/1.37              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 1.12/1.37          | ~ (v1_relat_1 @ X1)
% 1.12/1.37          | ~ (v1_relat_1 @ X0))),
% 1.12/1.37      inference('simplify', [status(thm)], ['38'])).
% 1.12/1.37  thf(t52_relat_1, conjecture,
% 1.12/1.37    (![A:$i]:
% 1.12/1.37     ( ( v1_relat_1 @ A ) =>
% 1.12/1.37       ( ![B:$i]:
% 1.12/1.37         ( ( v1_relat_1 @ B ) =>
% 1.12/1.37           ( ![C:$i]:
% 1.12/1.37             ( ( v1_relat_1 @ C ) =>
% 1.12/1.37               ( r1_tarski @
% 1.12/1.37                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 1.12/1.37                 ( k3_xboole_0 @
% 1.12/1.37                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.12/1.37  thf(zf_stmt_3, negated_conjecture,
% 1.12/1.37    (~( ![A:$i]:
% 1.12/1.37        ( ( v1_relat_1 @ A ) =>
% 1.12/1.37          ( ![B:$i]:
% 1.12/1.37            ( ( v1_relat_1 @ B ) =>
% 1.12/1.37              ( ![C:$i]:
% 1.12/1.37                ( ( v1_relat_1 @ C ) =>
% 1.12/1.37                  ( r1_tarski @
% 1.12/1.37                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 1.12/1.37                    ( k3_xboole_0 @
% 1.12/1.37                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 1.12/1.37    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 1.12/1.37  thf('40', plain,
% 1.12/1.37      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.12/1.37          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 1.12/1.37           (k5_relat_1 @ sk_A @ sk_C)))),
% 1.12/1.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.12/1.37  thf('41', plain,
% 1.12/1.37      (![X48 : $i, X49 : $i]:
% 1.12/1.37         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 1.12/1.37      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.12/1.37  thf('42', plain,
% 1.12/1.37      (![X48 : $i, X49 : $i]:
% 1.12/1.37         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 1.12/1.37      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.12/1.37  thf('43', plain,
% 1.12/1.37      (~ (r1_tarski @ 
% 1.12/1.37          (k5_relat_1 @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))) @ 
% 1.12/1.37          (k1_setfam_1 @ 
% 1.12/1.37           (k2_tarski @ (k5_relat_1 @ sk_A @ sk_B) @ (k5_relat_1 @ sk_A @ sk_C))))),
% 1.12/1.37      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.12/1.37  thf('44', plain,
% 1.12/1.37      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 1.12/1.37      inference('sup-', [status(thm)], ['39', '43'])).
% 1.12/1.37  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 1.12/1.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.12/1.37  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 1.12/1.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.12/1.37  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 1.12/1.37      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.12/1.37  thf('48', plain, ($false),
% 1.12/1.37      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 1.12/1.37  
% 1.12/1.37  % SZS output end Refutation
% 1.12/1.37  
% 1.12/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
