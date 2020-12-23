%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7je56u1hfN

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:28 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 233 expanded)
%              Number of leaves         :   33 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          :  665 (1491 expanded)
%              Number of equality atoms :   57 ( 125 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_relat_1_type,type,(
    v2_relat_1: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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

thf('0',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k7_funcop_1 @ X38 @ X39 )
      = ( k2_funcop_1 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('3',plain,(
    ! [X36: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k6_yellow_1 @ X32 @ X33 )
        = ( k5_yellow_1 @ X32 @ ( k7_funcop_1 @ X32 @ X33 ) ) )
      | ~ ( l1_orders_2 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
        = ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('8',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_zfmisc_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
        = ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
        = ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X1 )
        = ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('18',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('19',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( g1_orders_2 @ ( k1_zfmisc_1 @ X0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
       != ( g1_orders_2 @ ( k1_zfmisc_1 @ X1 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
       != ( g1_orders_2 @ ( k1_zfmisc_1 @ X1 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X1 )
       != ( g1_orders_2 @ ( k1_tarski @ X0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','25'])).

thf('27',plain,(
    ! [X36: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X1 )
       != ( g1_orders_2 @ ( k1_tarski @ X0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
       != ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
       != ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
       != ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
       != ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X34 @ X35 ) )
      | ~ ( l1_orders_2 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('40',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k7_funcop_1 @ X38 @ X39 )
      = ( k2_funcop_1 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('41',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X34 @ X35 ) )
      | ~ ( l1_orders_2 @ X35 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_yellow_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_yellow_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(rc4_funcop_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_partfun1 @ B @ A )
      & ( v1_funct_1 @ B )
      & ( v4_relat_1 @ B @ A )
      & ( v2_relat_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('46',plain,(
    ! [X37: $i] :
      ( v1_partfun1 @ ( sk_B @ X37 ) @ X37 ) ),
    inference(cnf,[status(esa)],[rc4_funcop_1])).

thf(t134_pboole,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('47',plain,(
    ! [X40: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( v1_partfun1 @ X40 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v4_relat_1 @ X40 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t134_pboole])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v4_relat_1 @ ( sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( sk_B @ X37 ) ) ),
    inference(cnf,[status(esa)],[rc4_funcop_1])).

thf('50',plain,(
    ! [X37: $i] :
      ( v4_relat_1 @ ( sk_B @ X37 ) @ X37 ) ),
    inference(cnf,[status(esa)],[rc4_funcop_1])).

thf('51',plain,(
    ! [X37: $i] :
      ( v1_funct_1 @ ( sk_B @ X37 ) ) ),
    inference(cnf,[status(esa)],[rc4_funcop_1])).

thf('52',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X37: $i] :
      ( v1_partfun1 @ ( sk_B @ X37 ) @ X37 ) ),
    inference(cnf,[status(esa)],[rc4_funcop_1])).

thf('54',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','54'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('56',plain,(
    ! [X41: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X41 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X41 )
      | ~ ( v1_partfun1 @ X41 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v4_relat_1 @ X41 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('57',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('58',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('59',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('60',plain,(
    ! [X41: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X41 )
        = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X41 )
      | ~ ( v1_partfun1 @ X41 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v4_relat_1 @ X41 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('63',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('64',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( sk_B @ X37 ) ) ),
    inference(cnf,[status(esa)],[rc4_funcop_1])).

thf('65',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['63','64'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('66',plain,(
    ! [X30: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X30 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('67',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('68',plain,(
    ! [X37: $i] :
      ( v1_funct_1 @ ( sk_B @ X37 ) ) ),
    inference(cnf,[status(esa)],[rc4_funcop_1])).

thf('69',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','65','66','69'])).

thf('71',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('73',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
       != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['35','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ~ ( l1_orders_2 @ X0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7je56u1hfN
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 221 iterations in 0.178s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.45/0.63  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.45/0.63  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.63  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.45/0.63  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.45/0.63  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.45/0.63  thf(v2_relat_1_type, type, v2_relat_1: $i > $o).
% 0.45/0.63  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.63  thf(t27_yellow_1, conjecture,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_orders_2 @ A ) =>
% 0.45/0.63       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.45/0.63         ( g1_orders_2 @
% 0.45/0.63           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.45/0.63           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i]:
% 0.45/0.63        ( ( l1_orders_2 @ A ) =>
% 0.45/0.63          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.45/0.63            ( g1_orders_2 @
% 0.45/0.63              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.45/0.63              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.45/0.63  thf('0', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(fc2_funcop_1, axiom,
% 0.45/0.63    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X36 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X36))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.45/0.63  thf(redefinition_k7_funcop_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X38 : $i, X39 : $i]:
% 0.45/0.63         ((k7_funcop_1 @ X38 @ X39) = (k2_funcop_1 @ X38 @ X39))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X36 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X36))),
% 0.45/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.63  thf(l13_xboole_0, axiom,
% 0.45/0.63    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf(d5_yellow_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( l1_orders_2 @ B ) =>
% 0.45/0.63       ( ( k6_yellow_1 @ A @ B ) =
% 0.45/0.63         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X32 : $i, X33 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ X32 @ X33)
% 0.45/0.63            = (k5_yellow_1 @ X32 @ (k7_funcop_1 @ X32 @ X33)))
% 0.45/0.63          | ~ (l1_orders_2 @ X33))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.45/0.63            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.45/0.63          | ~ (l1_orders_2 @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf(t1_zfmisc_1, axiom,
% 0.45/0.63    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.45/0.63  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.63  thf('10', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ X0))
% 0.45/0.63          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.45/0.63            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.45/0.63          | ~ (l1_orders_2 @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.45/0.63            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.45/0.63          | ~ (l1_orders_2 @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ X1) = (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.45/0.63          | ~ (l1_orders_2 @ X0)
% 0.45/0.63          | ~ (l1_orders_2 @ X1))),
% 0.45/0.63      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.45/0.63         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.45/0.63             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('17', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.63  thf('18', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.45/0.63         != (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63             (k6_partfun1 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.45/0.63      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.45/0.63  thf(redefinition_k6_partfun1, axiom,
% 0.45/0.63    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.45/0.63  thf('20', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.45/0.63         != (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63             (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.45/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.45/0.63            != (g1_orders_2 @ (k1_zfmisc_1 @ X0) @ 
% 0.45/0.63                (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.45/0.63          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['15', '21'])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.45/0.63            != (g1_orders_2 @ (k1_zfmisc_1 @ X1) @ 
% 0.45/0.63                (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.45/0.63          | ~ (l1_orders_2 @ X0)
% 0.45/0.63          | ~ (l1_orders_2 @ sk_A)
% 0.45/0.63          | ~ (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '22'])).
% 0.45/0.63  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.45/0.63            != (g1_orders_2 @ (k1_zfmisc_1 @ X1) @ 
% 0.45/0.63                (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.45/0.63          | ~ (l1_orders_2 @ X0)
% 0.45/0.63          | ~ (v1_xboole_0 @ X1))),
% 0.45/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ X1)
% 0.45/0.63            != (g1_orders_2 @ (k1_tarski @ X0) @ 
% 0.45/0.63                (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.45/0.63          | ~ (v1_xboole_0 @ X0)
% 0.45/0.63          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.63          | ~ (l1_orders_2 @ X1))),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '25'])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (![X36 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X36))),
% 0.45/0.63      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ X1)
% 0.45/0.63            != (g1_orders_2 @ (k1_tarski @ X0) @ 
% 0.45/0.63                (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.45/0.63          | ~ (v1_xboole_0 @ X0)
% 0.45/0.63          | ~ (l1_orders_2 @ X1))),
% 0.45/0.63      inference('demod', [status(thm)], ['26', '29'])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.45/0.63            != (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63                (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.45/0.63          | ~ (l1_orders_2 @ X0)
% 0.45/0.63          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['8', '30'])).
% 0.45/0.63  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.45/0.63            != (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63                (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.45/0.63          | ~ (l1_orders_2 @ X0))),
% 0.45/0.63      inference('demod', [status(thm)], ['31', '32'])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.63            != (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63                (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.45/0.63          | ~ (l1_orders_2 @ X0)
% 0.45/0.63          | ~ (l1_orders_2 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['7', '33'])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (l1_orders_2 @ X0)
% 0.45/0.63          | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.63              != (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63                  (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0)))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['34'])).
% 0.45/0.63  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf(fc10_yellow_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      (![X34 : $i, X35 : $i]:
% 0.45/0.63         ((v1_yellow_1 @ (k2_funcop_1 @ X34 @ X35)) | ~ (l1_orders_2 @ X35))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (![X38 : $i, X39 : $i]:
% 0.45/0.63         ((k7_funcop_1 @ X38 @ X39) = (k2_funcop_1 @ X38 @ X39))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      (![X34 : $i, X35 : $i]:
% 0.45/0.63         ((v1_yellow_1 @ (k7_funcop_1 @ X34 @ X35)) | ~ (l1_orders_2 @ X35))),
% 0.45/0.63      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['38', '41'])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((v1_yellow_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (l1_orders_2 @ X1))),
% 0.45/0.63      inference('sup+', [status(thm)], ['37', '42'])).
% 0.45/0.63  thf('44', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_yellow_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['36', '43'])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.63  thf(rc4_funcop_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ?[B:$i]:
% 0.45/0.63       ( ( v1_partfun1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 0.45/0.63         ( v4_relat_1 @ B @ A ) & ( v2_relat_1 @ B ) & ( v1_relat_1 @ B ) ) ))).
% 0.45/0.63  thf('46', plain, (![X37 : $i]: (v1_partfun1 @ (sk_B @ X37) @ X37)),
% 0.45/0.63      inference('cnf', [status(esa)], [rc4_funcop_1])).
% 0.45/0.63  thf(t134_pboole, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.45/0.63         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) ) =>
% 0.45/0.63       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      (![X40 : $i]:
% 0.45/0.63         (((X40) = (k1_xboole_0))
% 0.45/0.63          | ~ (v1_partfun1 @ X40 @ k1_xboole_0)
% 0.45/0.63          | ~ (v1_funct_1 @ X40)
% 0.45/0.63          | ~ (v4_relat_1 @ X40 @ k1_xboole_0)
% 0.45/0.63          | ~ (v1_relat_1 @ X40))),
% 0.45/0.63      inference('cnf', [status(esa)], [t134_pboole])).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.45/0.63        | ~ (v4_relat_1 @ (sk_B @ k1_xboole_0) @ k1_xboole_0)
% 0.45/0.63        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 0.45/0.63        | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.63  thf('49', plain, (![X37 : $i]: (v1_relat_1 @ (sk_B @ X37))),
% 0.45/0.63      inference('cnf', [status(esa)], [rc4_funcop_1])).
% 0.45/0.63  thf('50', plain, (![X37 : $i]: (v4_relat_1 @ (sk_B @ X37) @ X37)),
% 0.45/0.63      inference('cnf', [status(esa)], [rc4_funcop_1])).
% 0.45/0.63  thf('51', plain, (![X37 : $i]: (v1_funct_1 @ (sk_B @ X37))),
% 0.45/0.63      inference('cnf', [status(esa)], [rc4_funcop_1])).
% 0.45/0.63  thf('52', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.63      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.45/0.63  thf('53', plain, (![X37 : $i]: (v1_partfun1 @ (sk_B @ X37) @ X37)),
% 0.45/0.63      inference('cnf', [status(esa)], [rc4_funcop_1])).
% 0.45/0.63  thf('54', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('sup+', [status(thm)], ['52', '53'])).
% 0.45/0.63  thf('55', plain,
% 0.45/0.63      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['45', '54'])).
% 0.45/0.63  thf(t26_yellow_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.45/0.63         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.45/0.63         ( v1_yellow_1 @ A ) ) =>
% 0.45/0.63       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.45/0.63         ( g1_orders_2 @
% 0.45/0.63           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.45/0.63           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      (![X41 : $i]:
% 0.45/0.63         (((k5_yellow_1 @ k1_xboole_0 @ X41)
% 0.45/0.63            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.45/0.63               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.45/0.63          | ~ (v1_yellow_1 @ X41)
% 0.45/0.63          | ~ (v1_partfun1 @ X41 @ k1_xboole_0)
% 0.45/0.63          | ~ (v1_funct_1 @ X41)
% 0.45/0.63          | ~ (v4_relat_1 @ X41 @ k1_xboole_0)
% 0.45/0.63          | ~ (v1_relat_1 @ X41))),
% 0.45/0.63      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.45/0.63  thf('57', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.63  thf('58', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.63  thf('59', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      (![X41 : $i]:
% 0.45/0.63         (((k5_yellow_1 @ k1_xboole_0 @ X41)
% 0.45/0.63            = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63               (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.45/0.63          | ~ (v1_yellow_1 @ X41)
% 0.45/0.63          | ~ (v1_partfun1 @ X41 @ k1_xboole_0)
% 0.45/0.63          | ~ (v1_funct_1 @ X41)
% 0.45/0.63          | ~ (v4_relat_1 @ X41 @ k1_xboole_0)
% 0.45/0.63          | ~ (v1_relat_1 @ X41))),
% 0.45/0.63      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.45/0.63  thf('61', plain,
% 0.45/0.63      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.63        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.63        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.63        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.45/0.63        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.45/0.63        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.63            = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63               (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['55', '60'])).
% 0.45/0.63  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('63', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.63      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.45/0.63  thf('64', plain, (![X37 : $i]: (v1_relat_1 @ (sk_B @ X37))),
% 0.45/0.63      inference('cnf', [status(esa)], [rc4_funcop_1])).
% 0.45/0.63  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.63      inference('sup+', [status(thm)], ['63', '64'])).
% 0.45/0.63  thf(l222_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.45/0.63  thf('66', plain, (![X30 : $i]: (v4_relat_1 @ k1_xboole_0 @ X30)),
% 0.45/0.63      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.45/0.63  thf('67', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.63      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.45/0.63  thf('68', plain, (![X37 : $i]: (v1_funct_1 @ (sk_B @ X37))),
% 0.45/0.63      inference('cnf', [status(esa)], [rc4_funcop_1])).
% 0.45/0.63  thf('69', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.45/0.63      inference('sup+', [status(thm)], ['67', '68'])).
% 0.45/0.63  thf('70', plain,
% 0.45/0.63      ((~ (v1_yellow_1 @ k1_xboole_0)
% 0.45/0.63        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.63            = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63               (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0)))))),
% 0.45/0.63      inference('demod', [status(thm)], ['61', '62', '65', '66', '69'])).
% 0.45/0.63  thf('71', plain,
% 0.45/0.63      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.63        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.63            = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63               (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['44', '70'])).
% 0.45/0.63  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.63         = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.45/0.63            (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.45/0.63      inference('demod', [status(thm)], ['71', '72'])).
% 0.45/0.63  thf('74', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (l1_orders_2 @ X0)
% 0.45/0.63          | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.63              != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['35', '73'])).
% 0.45/0.63  thf('75', plain, (![X0 : $i]: ~ (l1_orders_2 @ X0)),
% 0.45/0.63      inference('simplify', [status(thm)], ['74'])).
% 0.45/0.63  thf('76', plain, ($false), inference('sup-', [status(thm)], ['0', '75'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
