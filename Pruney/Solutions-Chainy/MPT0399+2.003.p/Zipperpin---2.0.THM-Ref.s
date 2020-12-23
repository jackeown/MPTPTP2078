%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bfe5Aan1PV

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:56 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 171 expanded)
%              Number of leaves         :   42 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  651 ( 942 expanded)
%              Number of equality atoms :   52 (  92 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('0',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('1',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_setfam_1 @ X51 @ X52 )
      | ( r2_hidden @ ( sk_C @ X52 @ X51 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X54 ) @ ( k3_tarski @ X55 ) )
      | ~ ( r1_setfam_1 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ ( k3_tarski @ X1 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X38: $i] :
      ( ( k1_subset_1 @ X38 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('9',plain,(
    ! [X38: $i] :
      ( ( k1_subset_1 @ X38 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_subset_1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_subset_1 @ X1 ) )
      | ( X0
        = ( k1_subset_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X1
        = ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_tarski @ X0 )
        = ( k1_subset_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X38: $i] :
      ( ( k1_subset_1 @ X38 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('17',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X54 ) @ ( k3_tarski @ X55 ) )
      | ~ ( r1_setfam_1 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('19',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('21',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('26',plain,(
    ! [X34: $i] :
      ( r1_tarski @ X34 @ ( k1_zfmisc_1 @ ( k3_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('28',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36
        = ( k1_tarski @ X35 ) )
      | ( X36 = k1_xboole_0 )
      | ~ ( r1_tarski @ X36 @ ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A
      = ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( sk_A
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X38: $i] :
      ( ( k1_subset_1 @ X38 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('37',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X39 ) @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ k1_xboole_0 @ sk_A ),
    inference('sup+',[status(thm)],['35','38'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 )
      | ~ ( m1_subset_1 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_subset_1 @ X0 ) @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ X0 ) @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','42'])).

thf('44',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('45',plain,
    ( sk_A
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('46',plain,
    ( sk_A
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('47',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('49',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('52',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('53',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(fc7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) )).

thf('54',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc7_subset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ~ ( v1_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( v1_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( v1_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( v1_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ X0 ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','62'])).

thf('64',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','63'])).

thf('65',plain,(
    ! [X38: $i] :
      ( ( k1_subset_1 @ X38 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(fc13_subset_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ A ) ) )).

thf('66',plain,(
    ! [X40: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ ( sk_D @ X49 @ X50 ) @ X50 )
      | ~ ( r2_hidden @ X49 @ X51 )
      | ~ ( r1_setfam_1 @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['65','66'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bfe5Aan1PV
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 419 iterations in 0.171s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.41/0.62  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.41/0.62  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.41/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.41/0.62  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.41/0.62                                           $i > $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.41/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.62  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.41/0.62  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.41/0.62  thf('0', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.41/0.62  thf('1', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.41/0.62  thf(d2_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.41/0.62       ( ![C:$i]:
% 0.41/0.62         ( ~( ( r2_hidden @ C @ A ) & 
% 0.41/0.62              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X51 : $i, X52 : $i]:
% 0.41/0.62         ((r1_setfam_1 @ X51 @ X52) | (r2_hidden @ (sk_C @ X52 @ X51) @ X51))),
% 0.41/0.62      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.41/0.62  thf(t7_boole, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_boole])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ((r1_setfam_1 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.62  thf(t18_setfam_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r1_setfam_1 @ A @ B ) =>
% 0.41/0.62       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X54 : $i, X55 : $i]:
% 0.41/0.62         ((r1_tarski @ (k3_tarski @ X54) @ (k3_tarski @ X55))
% 0.41/0.62          | ~ (r1_setfam_1 @ X54 @ X55))),
% 0.41/0.62      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ X1)
% 0.41/0.62          | (r1_tarski @ (k3_tarski @ X1) @ (k3_tarski @ X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r1_tarski @ (k3_tarski @ X0) @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['1', '6'])).
% 0.41/0.62  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.62  thf('8', plain, (![X38 : $i]: ((k1_subset_1 @ X38) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.41/0.62  thf('9', plain, (![X38 : $i]: ((k1_subset_1 @ X38) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.41/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.62  thf('10', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k1_subset_1 @ X0) @ X1)),
% 0.41/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.41/0.62  thf(d10_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X0 : $i, X2 : $i]:
% 0.41/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r1_tarski @ X0 @ (k1_subset_1 @ X1)) | ((X0) = (k1_subset_1 @ X1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r1_tarski @ X1 @ k1_xboole_0) | ((X1) = (k1_subset_1 @ X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['8', '13'])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ X0) | ((k3_tarski @ X0) = (k1_subset_1 @ X1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['7', '14'])).
% 0.41/0.62  thf('16', plain, (![X38 : $i]: ((k1_subset_1 @ X38) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.41/0.62  thf(t21_setfam_1, conjecture,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i]:
% 0.41/0.62        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.41/0.62  thf('17', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X54 : $i, X55 : $i]:
% 0.41/0.62         ((r1_tarski @ (k3_tarski @ X54) @ (k3_tarski @ X55))
% 0.41/0.62          | ~ (r1_setfam_1 @ X54 @ X55))),
% 0.41/0.62      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ k1_xboole_0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.62  thf('20', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.41/0.62  thf('21', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ k1_xboole_0)),
% 0.41/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.62  thf('22', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X0 : $i, X2 : $i]:
% 0.41/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.62  thf('25', plain, (((k3_tarski @ sk_A) = (k1_xboole_0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['21', '24'])).
% 0.41/0.62  thf(t100_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (![X34 : $i]: (r1_tarski @ X34 @ (k1_zfmisc_1 @ (k3_tarski @ X34)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.41/0.62  thf('27', plain, ((r1_tarski @ sk_A @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['25', '26'])).
% 0.41/0.62  thf(t1_zfmisc_1, axiom,
% 0.41/0.62    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.41/0.62  thf('28', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.41/0.62  thf(t39_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.41/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X35 : $i, X36 : $i]:
% 0.41/0.62         (((X36) = (k1_tarski @ X35))
% 0.41/0.62          | ((X36) = (k1_xboole_0))
% 0.41/0.62          | ~ (r1_tarski @ X36 @ (k1_tarski @ X35)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r1_tarski @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.41/0.62          | ((X0) = (k1_xboole_0))
% 0.41/0.62          | ((X0) = (k1_tarski @ k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.62  thf('31', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r1_tarski @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.41/0.62          | ((X0) = (k1_xboole_0))
% 0.41/0.62          | ((X0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      ((((sk_A) = (k1_zfmisc_1 @ k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['27', '32'])).
% 0.41/0.62  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('35', plain, (((sk_A) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.41/0.62  thf('36', plain, (![X38 : $i]: ((k1_subset_1 @ X38) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.41/0.62  thf(dt_k1_subset_1, axiom,
% 0.41/0.62    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      (![X39 : $i]: (m1_subset_1 @ (k1_subset_1 @ X39) @ (k1_zfmisc_1 @ X39))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['36', '37'])).
% 0.41/0.62  thf('39', plain, ((m1_subset_1 @ k1_xboole_0 @ sk_A)),
% 0.41/0.62      inference('sup+', [status(thm)], ['35', '38'])).
% 0.41/0.62  thf(t2_subset, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.41/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.41/0.62  thf('40', plain,
% 0.41/0.62      (![X56 : $i, X57 : $i]:
% 0.41/0.62         ((r2_hidden @ X56 @ X57)
% 0.41/0.62          | (v1_xboole_0 @ X57)
% 0.41/0.62          | ~ (m1_subset_1 @ X56 @ X57))),
% 0.41/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.41/0.62  thf('41', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ k1_xboole_0 @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r2_hidden @ (k1_subset_1 @ X0) @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.41/0.62      inference('sup+', [status(thm)], ['16', '41'])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r2_hidden @ (k3_tarski @ X0) @ sk_A)
% 0.41/0.62          | ~ (v1_xboole_0 @ X0)
% 0.41/0.62          | (v1_xboole_0 @ sk_A))),
% 0.41/0.62      inference('sup+', [status(thm)], ['15', '42'])).
% 0.41/0.62  thf('44', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.41/0.62  thf('45', plain, (((sk_A) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.41/0.62  thf('46', plain, (((sk_A) = (k1_tarski @ k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.41/0.62  thf(t69_enumset1, axiom,
% 0.41/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.62  thf('47', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.41/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.62  thf(t70_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (![X7 : $i, X8 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.41/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.62  thf(t71_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.62         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.41/0.62      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.41/0.62  thf(t72_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.62         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.41/0.62           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.41/0.62      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.41/0.62  thf(t73_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.41/0.62     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.41/0.62       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.62         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.41/0.62           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.41/0.62      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.41/0.62  thf(t74_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.62     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.41/0.62       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.62         ((k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.41/0.62           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 0.41/0.62      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.41/0.62  thf(t75_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.41/0.62     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.41/0.62       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.41/0.62         ((k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.41/0.62           = (k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.41/0.62      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.41/0.62  thf(fc7_subset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.41/0.62     ( ~( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, 
% 0.41/0.62         X48 : $i]:
% 0.41/0.62         ~ (v1_xboole_0 @ 
% 0.41/0.62            (k6_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc7_subset_1])).
% 0.41/0.62  thf('55', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.62         ~ (v1_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.62  thf('56', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.62         ~ (v1_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.41/0.62  thf('57', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ~ (v1_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['51', '56'])).
% 0.41/0.62  thf('58', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         ~ (v1_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['50', '57'])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ~ (v1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['49', '58'])).
% 0.41/0.62  thf('60', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['48', '59'])).
% 0.41/0.62  thf('61', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['47', '60'])).
% 0.41/0.62  thf('62', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.41/0.62      inference('sup-', [status(thm)], ['46', '61'])).
% 0.41/0.62  thf('63', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ X0) | (r2_hidden @ (k3_tarski @ X0) @ sk_A))),
% 0.41/0.62      inference('clc', [status(thm)], ['43', '62'])).
% 0.41/0.62  thf('64', plain,
% 0.41/0.62      (((r2_hidden @ k1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['0', '63'])).
% 0.41/0.62  thf('65', plain, (![X38 : $i]: ((k1_subset_1 @ X38) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.41/0.62  thf(fc13_subset_1, axiom, (![A:$i]: ( v1_xboole_0 @ ( k1_subset_1 @ A ) ))).
% 0.41/0.62  thf('66', plain, (![X40 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X40))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc13_subset_1])).
% 0.41/0.62  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('sup+', [status(thm)], ['65', '66'])).
% 0.41/0.62  thf('68', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['64', '67'])).
% 0.41/0.62  thf('69', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('70', plain,
% 0.41/0.62      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.41/0.62         ((r2_hidden @ (sk_D @ X49 @ X50) @ X50)
% 0.41/0.62          | ~ (r2_hidden @ X49 @ X51)
% 0.41/0.62          | ~ (r1_setfam_1 @ X51 @ X50))),
% 0.41/0.62      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.41/0.62  thf('71', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.62          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['69', '70'])).
% 0.41/0.62  thf('72', plain,
% 0.41/0.62      ((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.41/0.62      inference('sup-', [status(thm)], ['68', '71'])).
% 0.41/0.62  thf('73', plain,
% 0.41/0.62      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_boole])).
% 0.41/0.62  thf('74', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.41/0.62  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('sup+', [status(thm)], ['65', '66'])).
% 0.41/0.62  thf('76', plain, ($false), inference('demod', [status(thm)], ['74', '75'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.41/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
