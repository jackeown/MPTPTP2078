%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vEHtaD50rX

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:09 EST 2020

% Result     : Theorem 38.72s
% Output     : Refutation 38.72s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 148 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  652 (1311 expanded)
%              Number of equality atoms :   22 (  50 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) @ X3 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X52 @ X54 )
      | ( r1_tarski @ ( k1_setfam_1 @ X53 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('16',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','18'])).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','18'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) @ X3 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

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
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) @ X3 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

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

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
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
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45','46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vEHtaD50rX
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 38.72/38.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 38.72/38.98  % Solved by: fo/fo7.sh
% 38.72/38.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 38.72/38.98  % done 16503 iterations in 38.518s
% 38.72/38.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 38.72/38.98  % SZS output start Refutation
% 38.72/38.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 38.72/38.98  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 38.72/38.98  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 38.72/38.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 38.72/38.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 38.72/38.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 38.72/38.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 38.72/38.98  thf(sk_B_type, type, sk_B: $i).
% 38.72/38.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 38.72/38.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 38.72/38.98  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 38.72/38.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 38.72/38.98  thf(sk_C_type, type, sk_C: $i).
% 38.72/38.98  thf(sk_A_type, type, sk_A: $i).
% 38.72/38.98  thf(t17_xboole_1, axiom,
% 38.72/38.98    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 38.72/38.98  thf('0', plain,
% 38.72/38.98      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 38.72/38.98      inference('cnf', [status(esa)], [t17_xboole_1])).
% 38.72/38.98  thf(t12_setfam_1, axiom,
% 38.72/38.98    (![A:$i,B:$i]:
% 38.72/38.98     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 38.72/38.98  thf('1', plain,
% 38.72/38.98      (![X47 : $i, X48 : $i]:
% 38.72/38.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 38.72/38.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.98  thf('2', plain,
% 38.72/38.98      (![X3 : $i, X4 : $i]:
% 38.72/38.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 38.72/38.98      inference('demod', [status(thm)], ['0', '1'])).
% 38.72/38.98  thf(d10_xboole_0, axiom,
% 38.72/38.98    (![A:$i,B:$i]:
% 38.72/38.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 38.72/38.98  thf('3', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 38.72/38.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 38.72/38.98  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 38.72/38.98      inference('simplify', [status(thm)], ['3'])).
% 38.72/38.98  thf(t70_enumset1, axiom,
% 38.72/38.98    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 38.72/38.98  thf('5', plain,
% 38.72/38.98      (![X20 : $i, X21 : $i]:
% 38.72/38.98         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 38.72/38.98      inference('cnf', [status(esa)], [t70_enumset1])).
% 38.72/38.98  thf(d1_enumset1, axiom,
% 38.72/38.98    (![A:$i,B:$i,C:$i,D:$i]:
% 38.72/38.98     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 38.72/38.98       ( ![E:$i]:
% 38.72/38.98         ( ( r2_hidden @ E @ D ) <=>
% 38.72/38.98           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 38.72/38.98  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 38.72/38.98  thf(zf_stmt_1, axiom,
% 38.72/38.98    (![E:$i,C:$i,B:$i,A:$i]:
% 38.72/38.98     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 38.72/38.98       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 38.72/38.98  thf(zf_stmt_2, axiom,
% 38.72/38.98    (![A:$i,B:$i,C:$i,D:$i]:
% 38.72/38.98     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 38.72/38.98       ( ![E:$i]:
% 38.72/38.98         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 38.72/38.98  thf('6', plain,
% 38.72/38.98      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 38.72/38.98         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 38.72/38.98          | (r2_hidden @ X13 @ X17)
% 38.72/38.98          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 38.72/38.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 38.72/38.98  thf('7', plain,
% 38.72/38.98      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 38.72/38.98         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 38.72/38.98          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 38.72/38.98      inference('simplify', [status(thm)], ['6'])).
% 38.72/38.98  thf('8', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.98         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 38.72/38.98          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 38.72/38.98      inference('sup+', [status(thm)], ['5', '7'])).
% 38.72/38.98  thf('9', plain,
% 38.72/38.98      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 38.72/38.98         (((X9) != (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 38.72/38.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 38.72/38.98  thf('10', plain,
% 38.72/38.98      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X10 @ X10 @ X11 @ X8)),
% 38.72/38.98      inference('simplify', [status(thm)], ['9'])).
% 38.72/38.98  thf('11', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 38.72/38.98      inference('sup-', [status(thm)], ['8', '10'])).
% 38.72/38.98  thf(t8_setfam_1, axiom,
% 38.72/38.98    (![A:$i,B:$i,C:$i]:
% 38.72/38.98     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 38.72/38.98       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 38.72/38.98  thf('12', plain,
% 38.72/38.98      (![X52 : $i, X53 : $i, X54 : $i]:
% 38.72/38.98         (~ (r2_hidden @ X52 @ X53)
% 38.72/38.98          | ~ (r1_tarski @ X52 @ X54)
% 38.72/38.98          | (r1_tarski @ (k1_setfam_1 @ X53) @ X54))),
% 38.72/38.98      inference('cnf', [status(esa)], [t8_setfam_1])).
% 38.72/38.98  thf('13', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.98         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 38.72/38.98          | ~ (r1_tarski @ X0 @ X2))),
% 38.72/38.98      inference('sup-', [status(thm)], ['11', '12'])).
% 38.72/38.98  thf('14', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i]:
% 38.72/38.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 38.72/38.98      inference('sup-', [status(thm)], ['4', '13'])).
% 38.72/38.98  thf(t19_xboole_1, axiom,
% 38.72/38.98    (![A:$i,B:$i,C:$i]:
% 38.72/38.98     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 38.72/38.98       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 38.72/38.98  thf('15', plain,
% 38.72/38.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 38.72/38.98         (~ (r1_tarski @ X5 @ X6)
% 38.72/38.98          | ~ (r1_tarski @ X5 @ X7)
% 38.72/38.98          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 38.72/38.98      inference('cnf', [status(esa)], [t19_xboole_1])).
% 38.72/38.98  thf('16', plain,
% 38.72/38.98      (![X47 : $i, X48 : $i]:
% 38.72/38.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 38.72/38.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.98  thf('17', plain,
% 38.72/38.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 38.72/38.98         (~ (r1_tarski @ X5 @ X6)
% 38.72/38.98          | ~ (r1_tarski @ X5 @ X7)
% 38.72/38.98          | (r1_tarski @ X5 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 38.72/38.98      inference('demod', [status(thm)], ['15', '16'])).
% 38.72/38.98  thf('18', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.98         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 38.72/38.98           (k1_setfam_1 @ (k2_tarski @ X0 @ X2)))
% 38.72/38.98          | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2))),
% 38.72/38.98      inference('sup-', [status(thm)], ['14', '17'])).
% 38.72/38.98  thf('19', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i]:
% 38.72/38.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 38.72/38.98          (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 38.72/38.98      inference('sup-', [status(thm)], ['2', '18'])).
% 38.72/38.98  thf('20', plain,
% 38.72/38.98      (![X0 : $i, X2 : $i]:
% 38.72/38.98         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 38.72/38.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 38.72/38.98  thf('21', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i]:
% 38.72/38.98         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 38.72/38.98             (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 38.72/38.98          | ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 38.72/38.98              = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 38.72/38.98      inference('sup-', [status(thm)], ['19', '20'])).
% 38.72/38.98  thf('22', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i]:
% 38.72/38.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 38.72/38.98          (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 38.72/38.98      inference('sup-', [status(thm)], ['2', '18'])).
% 38.72/38.98  thf('23', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i]:
% 38.72/38.98         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 38.72/38.98           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 38.72/38.98      inference('demod', [status(thm)], ['21', '22'])).
% 38.72/38.98  thf('24', plain,
% 38.72/38.98      (![X3 : $i, X4 : $i]:
% 38.72/38.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 38.72/38.98      inference('demod', [status(thm)], ['0', '1'])).
% 38.72/38.98  thf(t3_subset, axiom,
% 38.72/38.98    (![A:$i,B:$i]:
% 38.72/38.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 38.72/38.98  thf('25', plain,
% 38.72/38.98      (![X49 : $i, X51 : $i]:
% 38.72/38.98         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 38.72/38.98      inference('cnf', [status(esa)], [t3_subset])).
% 38.72/38.98  thf('26', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i]:
% 38.72/38.98         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 38.72/38.98          (k1_zfmisc_1 @ X0))),
% 38.72/38.98      inference('sup-', [status(thm)], ['24', '25'])).
% 38.72/38.98  thf(cc2_relat_1, axiom,
% 38.72/38.98    (![A:$i]:
% 38.72/38.98     ( ( v1_relat_1 @ A ) =>
% 38.72/38.98       ( ![B:$i]:
% 38.72/38.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 38.72/38.98  thf('27', plain,
% 38.72/38.98      (![X55 : $i, X56 : $i]:
% 38.72/38.98         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X56))
% 38.72/38.98          | (v1_relat_1 @ X55)
% 38.72/38.98          | ~ (v1_relat_1 @ X56))),
% 38.72/38.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 38.72/38.98  thf('28', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i]:
% 38.72/38.98         (~ (v1_relat_1 @ X0)
% 38.72/38.98          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 38.72/38.98      inference('sup-', [status(thm)], ['26', '27'])).
% 38.72/38.98  thf('29', plain,
% 38.72/38.98      (![X3 : $i, X4 : $i]:
% 38.72/38.98         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4)) @ X3)),
% 38.72/38.98      inference('demod', [status(thm)], ['0', '1'])).
% 38.72/38.98  thf(t48_relat_1, axiom,
% 38.72/38.98    (![A:$i]:
% 38.72/38.98     ( ( v1_relat_1 @ A ) =>
% 38.72/38.98       ( ![B:$i]:
% 38.72/38.98         ( ( v1_relat_1 @ B ) =>
% 38.72/38.98           ( ![C:$i]:
% 38.72/38.98             ( ( v1_relat_1 @ C ) =>
% 38.72/38.98               ( ( r1_tarski @ A @ B ) =>
% 38.72/38.98                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 38.72/38.98  thf('30', plain,
% 38.72/38.98      (![X57 : $i, X58 : $i, X59 : $i]:
% 38.72/38.98         (~ (v1_relat_1 @ X57)
% 38.72/38.98          | ~ (r1_tarski @ X58 @ X57)
% 38.72/38.98          | (r1_tarski @ (k5_relat_1 @ X59 @ X58) @ (k5_relat_1 @ X59 @ X57))
% 38.72/38.98          | ~ (v1_relat_1 @ X59)
% 38.72/38.98          | ~ (v1_relat_1 @ X58))),
% 38.72/38.98      inference('cnf', [status(esa)], [t48_relat_1])).
% 38.72/38.98  thf('31', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.98         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 38.72/38.98          | ~ (v1_relat_1 @ X2)
% 38.72/38.98          | (r1_tarski @ 
% 38.72/38.98             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 38.72/38.98             (k5_relat_1 @ X2 @ X0))
% 38.72/38.98          | ~ (v1_relat_1 @ X0))),
% 38.72/38.98      inference('sup-', [status(thm)], ['29', '30'])).
% 38.72/38.98  thf('32', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.98         (~ (v1_relat_1 @ X1)
% 38.72/38.98          | ~ (v1_relat_1 @ X1)
% 38.72/38.98          | (r1_tarski @ 
% 38.72/38.98             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 38.72/38.98             (k5_relat_1 @ X2 @ X1))
% 38.72/38.98          | ~ (v1_relat_1 @ X2))),
% 38.72/38.98      inference('sup-', [status(thm)], ['28', '31'])).
% 38.72/38.98  thf('33', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.98         (~ (v1_relat_1 @ X2)
% 38.72/38.98          | (r1_tarski @ 
% 38.72/38.98             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 38.72/38.98             (k5_relat_1 @ X2 @ X1))
% 38.72/38.98          | ~ (v1_relat_1 @ X1))),
% 38.72/38.98      inference('simplify', [status(thm)], ['32'])).
% 38.72/38.98  thf('34', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.98         ((r1_tarski @ 
% 38.72/38.98           (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 38.72/38.98           (k5_relat_1 @ X2 @ X0))
% 38.72/38.98          | ~ (v1_relat_1 @ X0)
% 38.72/38.98          | ~ (v1_relat_1 @ X2))),
% 38.72/38.98      inference('sup+', [status(thm)], ['23', '33'])).
% 38.72/38.98  thf('35', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.98         (~ (v1_relat_1 @ X2)
% 38.72/38.98          | (r1_tarski @ 
% 38.72/38.98             (k5_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 38.72/38.98             (k5_relat_1 @ X2 @ X1))
% 38.72/38.98          | ~ (v1_relat_1 @ X1))),
% 38.72/38.98      inference('simplify', [status(thm)], ['32'])).
% 38.72/38.98  thf('36', plain,
% 38.72/38.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 38.72/38.98         (~ (r1_tarski @ X5 @ X6)
% 38.72/38.98          | ~ (r1_tarski @ X5 @ X7)
% 38.72/38.98          | (r1_tarski @ X5 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 38.72/38.98      inference('demod', [status(thm)], ['15', '16'])).
% 38.72/38.98  thf('37', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 38.72/38.98         (~ (v1_relat_1 @ X0)
% 38.72/38.98          | ~ (v1_relat_1 @ X1)
% 38.72/38.98          | (r1_tarski @ 
% 38.72/38.98             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ 
% 38.72/38.98             (k1_setfam_1 @ (k2_tarski @ (k5_relat_1 @ X1 @ X0) @ X3)))
% 38.72/38.98          | ~ (r1_tarski @ 
% 38.72/38.98               (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X2))) @ X3))),
% 38.72/38.98      inference('sup-', [status(thm)], ['35', '36'])).
% 38.72/38.98  thf('38', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.98         (~ (v1_relat_1 @ X1)
% 38.72/38.98          | ~ (v1_relat_1 @ X0)
% 38.72/38.98          | (r1_tarski @ 
% 38.72/38.98             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 38.72/38.98             (k1_setfam_1 @ 
% 38.72/38.98              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 38.72/38.98          | ~ (v1_relat_1 @ X1)
% 38.72/38.98          | ~ (v1_relat_1 @ X2))),
% 38.72/38.98      inference('sup-', [status(thm)], ['34', '37'])).
% 38.72/38.98  thf('39', plain,
% 38.72/38.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.98         (~ (v1_relat_1 @ X2)
% 38.72/38.98          | (r1_tarski @ 
% 38.72/38.98             (k5_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 38.72/38.98             (k1_setfam_1 @ 
% 38.72/38.98              (k2_tarski @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0))))
% 38.72/38.98          | ~ (v1_relat_1 @ X0)
% 38.72/38.98          | ~ (v1_relat_1 @ X1))),
% 38.72/38.98      inference('simplify', [status(thm)], ['38'])).
% 38.72/38.98  thf(t52_relat_1, conjecture,
% 38.72/38.98    (![A:$i]:
% 38.72/38.98     ( ( v1_relat_1 @ A ) =>
% 38.72/38.98       ( ![B:$i]:
% 38.72/38.98         ( ( v1_relat_1 @ B ) =>
% 38.72/38.98           ( ![C:$i]:
% 38.72/38.98             ( ( v1_relat_1 @ C ) =>
% 38.72/38.98               ( r1_tarski @
% 38.72/38.98                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 38.72/38.98                 ( k3_xboole_0 @
% 38.72/38.98                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 38.72/38.98  thf(zf_stmt_3, negated_conjecture,
% 38.72/38.98    (~( ![A:$i]:
% 38.72/38.98        ( ( v1_relat_1 @ A ) =>
% 38.72/38.98          ( ![B:$i]:
% 38.72/38.98            ( ( v1_relat_1 @ B ) =>
% 38.72/38.98              ( ![C:$i]:
% 38.72/38.98                ( ( v1_relat_1 @ C ) =>
% 38.72/38.98                  ( r1_tarski @
% 38.72/38.98                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 38.72/38.98                    ( k3_xboole_0 @
% 38.72/38.98                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 38.72/38.98    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 38.72/38.98  thf('40', plain,
% 38.72/38.98      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 38.72/38.98          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 38.72/38.98           (k5_relat_1 @ sk_A @ sk_C)))),
% 38.72/38.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 38.72/38.98  thf('41', plain,
% 38.72/38.98      (![X47 : $i, X48 : $i]:
% 38.72/38.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 38.72/38.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.98  thf('42', plain,
% 38.72/38.98      (![X47 : $i, X48 : $i]:
% 38.72/38.98         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 38.72/38.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.98  thf('43', plain,
% 38.72/38.98      (~ (r1_tarski @ 
% 38.72/38.98          (k5_relat_1 @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))) @ 
% 38.72/38.98          (k1_setfam_1 @ 
% 38.72/38.98           (k2_tarski @ (k5_relat_1 @ sk_A @ sk_B) @ (k5_relat_1 @ sk_A @ sk_C))))),
% 38.72/38.98      inference('demod', [status(thm)], ['40', '41', '42'])).
% 38.72/38.98  thf('44', plain,
% 38.72/38.98      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 38.72/38.98      inference('sup-', [status(thm)], ['39', '43'])).
% 38.72/38.98  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 38.72/38.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 38.72/38.98  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 38.72/38.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 38.72/38.98  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 38.72/38.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 38.72/38.98  thf('48', plain, ($false),
% 38.72/38.98      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 38.72/38.98  
% 38.72/38.98  % SZS output end Refutation
% 38.72/38.98  
% 38.72/38.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
