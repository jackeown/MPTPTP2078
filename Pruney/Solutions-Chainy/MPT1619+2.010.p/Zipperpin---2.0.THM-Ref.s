%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wtDtaBG0ah

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:25 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 188 expanded)
%              Number of leaves         :   41 (  80 expanded)
%              Depth                    :   17
%              Number of atoms          :  546 ( 971 expanded)
%              Number of equality atoms :   48 ( 103 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k6_yellow_1 @ X45 @ X46 )
        = ( k5_yellow_1 @ X45 @ ( k7_funcop_1 @ X45 @ X46 ) ) )
      | ~ ( l1_orders_2 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t27_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k6_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ( ( k6_yellow_1 @ k1_xboole_0 @ A )
          = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_yellow_1])).

thf('2',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('3',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X44: $i] :
      ( ( k9_setfam_1 @ X44 )
      = ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('5',plain,
    ( ( k9_setfam_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k9_setfam_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('7',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k9_setfam_1 @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k9_setfam_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['2','5','6'])).

thf('8',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ( v4_relat_1 @ X37 @ X38 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('17',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('18',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X39 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','25'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('27',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k1_relat_1 @ X42 )
       != X41 )
      | ( v1_partfun1 @ X42 @ X41 )
      | ~ ( v4_relat_1 @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('28',plain,(
    ! [X42: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v4_relat_1 @ X42 @ ( k1_relat_1 @ X42 ) )
      | ( v1_partfun1 @ X42 @ ( k1_relat_1 @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( v1_partfun1 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','22'])).

thf('34',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','34'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('36',plain,(
    ! [X52: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X52 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X52 )
      | ~ ( v1_partfun1 @ X52 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v4_relat_1 @ X52 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('37',plain,
    ( ( k9_setfam_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('38',plain,
    ( ( k9_setfam_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('39',plain,(
    ! [X52: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X52 )
        = ( g1_orders_2 @ ( k9_setfam_1 @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k9_setfam_1 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X52 )
      | ~ ( v1_partfun1 @ X52 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v4_relat_1 @ X52 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k9_setfam_1 @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k9_setfam_1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','22'])).

thf('43',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','24'])).

thf('44',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18'])).

thf('45',plain,(
    ! [X40: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('47',plain,(
    ! [X40: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X40 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('50',plain,(
    ! [X49: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('51',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X47 @ X48 ) )
      | ~ ( l1_orders_2 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k9_setfam_1 @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k9_setfam_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','48','55'])).

thf('57',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k5_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('61',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k7_funcop_1 @ X50 @ X51 )
      = ( k2_funcop_1 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62','63'])).

thf('65',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['64'])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wtDtaBG0ah
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 289 iterations in 0.215s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.67  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.45/0.67  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.45/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.67  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.45/0.67  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.67  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.45/0.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.67  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.45/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(d5_yellow_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( l1_orders_2 @ B ) =>
% 0.45/0.67       ( ( k6_yellow_1 @ A @ B ) =
% 0.45/0.67         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (![X45 : $i, X46 : $i]:
% 0.45/0.67         (((k6_yellow_1 @ X45 @ X46)
% 0.45/0.67            = (k5_yellow_1 @ X45 @ (k7_funcop_1 @ X45 @ X46)))
% 0.45/0.67          | ~ (l1_orders_2 @ X46))),
% 0.45/0.67      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.45/0.67  thf(l13_xboole_0, axiom,
% 0.45/0.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.67  thf(t27_yellow_1, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_orders_2 @ A ) =>
% 0.45/0.67       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.45/0.67         ( g1_orders_2 @
% 0.45/0.67           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.45/0.67           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( l1_orders_2 @ A ) =>
% 0.45/0.67          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.45/0.67            ( g1_orders_2 @
% 0.45/0.67              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.45/0.67              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.45/0.67         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.45/0.67             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t1_zfmisc_1, axiom,
% 0.45/0.67    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.45/0.67  thf('3', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.67  thf(redefinition_k9_setfam_1, axiom,
% 0.45/0.67    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.67  thf('4', plain, (![X44 : $i]: ((k9_setfam_1 @ X44) = (k1_zfmisc_1 @ X44))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.45/0.67  thf('5', plain, (((k9_setfam_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf('6', plain, (((k9_setfam_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.45/0.67         != (g1_orders_2 @ (k9_setfam_1 @ k1_xboole_0) @ 
% 0.45/0.67             (k6_partfun1 @ (k9_setfam_1 @ k1_xboole_0))))),
% 0.45/0.67      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.67  thf(d3_tarski, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X4 : $i, X6 : $i]:
% 0.45/0.67         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X4 : $i, X6 : $i]:
% 0.45/0.67         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.67  thf('13', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.45/0.67      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.67  thf(t60_relat_1, axiom,
% 0.45/0.67    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.67     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.67  thf('14', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.67  thf(d18_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ B ) =>
% 0.45/0.67       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X37 : $i, X38 : $i]:
% 0.45/0.67         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 0.45/0.67          | (v4_relat_1 @ X37 @ X38)
% 0.45/0.67          | ~ (v1_relat_1 @ X37))),
% 0.45/0.67      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.67          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.67  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.45/0.67  thf('17', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.45/0.67  thf(redefinition_k6_partfun1, axiom,
% 0.45/0.67    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.45/0.67  thf('18', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.67  thf('19', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf(fc3_funct_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.45/0.67       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.45/0.67  thf('20', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.67  thf('21', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.67  thf('22', plain, (![X39 : $i]: (v1_relat_1 @ (k6_partfun1 @ X39))),
% 0.45/0.67      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.67  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.67      inference('sup+', [status(thm)], ['19', '22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (r1_tarski @ k1_xboole_0 @ X0) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['16', '23'])).
% 0.45/0.67  thf('25', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['13', '24'])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X0 : $i]: ((v4_relat_1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['9', '25'])).
% 0.45/0.67  thf(d4_partfun1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.67       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X41 : $i, X42 : $i]:
% 0.45/0.67         (((k1_relat_1 @ X42) != (X41))
% 0.45/0.67          | (v1_partfun1 @ X42 @ X41)
% 0.45/0.67          | ~ (v4_relat_1 @ X42 @ X41)
% 0.45/0.67          | ~ (v1_relat_1 @ X42))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X42 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X42)
% 0.45/0.67          | ~ (v4_relat_1 @ X42 @ (k1_relat_1 @ X42))
% 0.45/0.67          | (v1_partfun1 @ X42 @ (k1_relat_1 @ X42)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['27'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      ((~ (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.45/0.67        | (v1_partfun1 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.45/0.67        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['26', '28'])).
% 0.45/0.67  thf('30', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.67  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.67  thf('32', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.67  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.67      inference('sup+', [status(thm)], ['19', '22'])).
% 0.45/0.67  thf('34', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['8', '34'])).
% 0.45/0.67  thf(t26_yellow_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.45/0.67         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.45/0.67         ( v1_yellow_1 @ A ) ) =>
% 0.45/0.67       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.45/0.67         ( g1_orders_2 @
% 0.45/0.67           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.45/0.67           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X52 : $i]:
% 0.45/0.67         (((k5_yellow_1 @ k1_xboole_0 @ X52)
% 0.45/0.67            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.45/0.67               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.45/0.67          | ~ (v1_yellow_1 @ X52)
% 0.45/0.67          | ~ (v1_partfun1 @ X52 @ k1_xboole_0)
% 0.45/0.67          | ~ (v1_funct_1 @ X52)
% 0.45/0.67          | ~ (v4_relat_1 @ X52 @ k1_xboole_0)
% 0.45/0.67          | ~ (v1_relat_1 @ X52))),
% 0.45/0.67      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.45/0.67  thf('37', plain, (((k9_setfam_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf('38', plain, (((k9_setfam_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (![X52 : $i]:
% 0.45/0.67         (((k5_yellow_1 @ k1_xboole_0 @ X52)
% 0.45/0.67            = (g1_orders_2 @ (k9_setfam_1 @ k1_xboole_0) @ 
% 0.45/0.67               (k6_partfun1 @ (k9_setfam_1 @ k1_xboole_0))))
% 0.45/0.67          | ~ (v1_yellow_1 @ X52)
% 0.45/0.67          | ~ (v1_partfun1 @ X52 @ k1_xboole_0)
% 0.45/0.67          | ~ (v1_funct_1 @ X52)
% 0.45/0.67          | ~ (v4_relat_1 @ X52 @ k1_xboole_0)
% 0.45/0.67          | ~ (v1_relat_1 @ X52))),
% 0.45/0.67      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.67        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.67        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.67        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.45/0.67        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.45/0.67        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.67            = (g1_orders_2 @ (k9_setfam_1 @ k1_xboole_0) @ 
% 0.45/0.67               (k6_partfun1 @ (k9_setfam_1 @ k1_xboole_0)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['35', '39'])).
% 0.45/0.67  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.67  thf('42', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.67      inference('sup+', [status(thm)], ['19', '22'])).
% 0.45/0.67  thf('43', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['13', '24'])).
% 0.45/0.67  thf('44', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.67  thf('45', plain, (![X40 : $i]: (v1_funct_1 @ (k6_relat_1 @ X40))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.45/0.67  thf('46', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.67  thf('47', plain, (![X40 : $i]: (v1_funct_1 @ (k6_partfun1 @ X40))),
% 0.45/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.67  thf('48', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.45/0.67      inference('sup+', [status(thm)], ['44', '47'])).
% 0.45/0.67  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(fc2_funcop_1, axiom,
% 0.45/0.67    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      (![X49 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X49))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.45/0.67  thf('51', plain,
% 0.45/0.67      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.45/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf(fc10_yellow_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (![X47 : $i, X48 : $i]:
% 0.45/0.67         ((v1_yellow_1 @ (k2_funcop_1 @ X47 @ X48)) | ~ (l1_orders_2 @ X48))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['52', '53'])).
% 0.45/0.67  thf('55', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['49', '54'])).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.67         = (g1_orders_2 @ (k9_setfam_1 @ k1_xboole_0) @ 
% 0.45/0.67            (k6_partfun1 @ (k9_setfam_1 @ k1_xboole_0))))),
% 0.45/0.67      inference('demod', [status(thm)], ['40', '41', '42', '43', '48', '55'])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.45/0.67         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['7', '56'])).
% 0.45/0.67  thf('58', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.45/0.67            != (k5_yellow_1 @ k1_xboole_0 @ X0))
% 0.45/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '57'])).
% 0.45/0.67  thf('59', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.45/0.67            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.45/0.67          | ~ (l1_orders_2 @ X0)
% 0.45/0.67          | ~ (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['0', '58'])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.67  thf(redefinition_k7_funcop_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.45/0.67  thf('61', plain,
% 0.45/0.67      (![X50 : $i, X51 : $i]:
% 0.45/0.67         ((k7_funcop_1 @ X50 @ X51) = (k2_funcop_1 @ X50 @ X51))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.45/0.67  thf('62', plain,
% 0.45/0.67      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.67  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.67  thf('64', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.45/0.67            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.45/0.67          | ~ (l1_orders_2 @ X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['59', '62', '63'])).
% 0.45/0.67  thf('65', plain, (~ (l1_orders_2 @ sk_A)),
% 0.45/0.67      inference('eq_res', [status(thm)], ['64'])).
% 0.45/0.67  thf('66', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('67', plain, ($false), inference('demod', [status(thm)], ['65', '66'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
