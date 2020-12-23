%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gs7PJM8I5o

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:25 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 110 expanded)
%              Number of leaves         :   42 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  419 ( 533 expanded)
%              Number of equality atoms :   35 (  50 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k7_funcop_1 @ X36 @ X37 )
      = ( k2_funcop_1 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k6_yellow_1 @ X31 @ X32 )
        = ( k5_yellow_1 @ X31 @ ( k7_funcop_1 @ X31 @ X32 ) ) )
      | ~ ( l1_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
        = ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('11',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('13',plain,(
    ! [X28: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('14',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X28: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X28 ) @ X28 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('17',plain,(
    ! [X38: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X38 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X38 )
      | ~ ( v1_partfun1 @ X38 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v4_relat_1 @ X38 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('18',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X38: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X38 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X38 )
      | ~ ( v1_partfun1 @ X38 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v4_relat_1 @ X38 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('32',plain,(
    ! [X27: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['31','32'])).

thf(rc4_orders_2,axiom,(
    ? [A: $i] :
      ( ( v1_orders_2 @ A )
      & ( v2_struct_0 @ A )
      & ( l1_orders_2 @ A ) ) )).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[rc4_orders_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X33 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('37',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k7_funcop_1 @ X36 @ X37 )
      = ( k2_funcop_1 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('38',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X33 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','24','30','33','40'])).

thf('42',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','42'])).

thf('44',plain,(
    ~ ( l1_orders_2 @ sk_A_1 ) ),
    inference(eq_res,[status(thm)],['43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gs7PJM8I5o
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 192 iterations in 0.151s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.39/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.60  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.39/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.60  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.39/0.60  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.60  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.39/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.60  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.39/0.60  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.39/0.60  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.39/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.60  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.39/0.60  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.39/0.60  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.39/0.60  thf(fc2_funcop_1, axiom,
% 0.39/0.60    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      (![X35 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X35))),
% 0.39/0.60      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.39/0.60  thf(l13_xboole_0, axiom,
% 0.39/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf(redefinition_k7_funcop_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      (![X36 : $i, X37 : $i]:
% 0.39/0.60         ((k7_funcop_1 @ X36 @ X37) = (k2_funcop_1 @ X36 @ X37))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.60  thf(d5_yellow_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( l1_orders_2 @ B ) =>
% 0.39/0.60       ( ( k6_yellow_1 @ A @ B ) =
% 0.39/0.60         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      (![X31 : $i, X32 : $i]:
% 0.39/0.60         (((k6_yellow_1 @ X31 @ X32)
% 0.39/0.60            = (k5_yellow_1 @ X31 @ (k7_funcop_1 @ X31 @ X32)))
% 0.39/0.60          | ~ (l1_orders_2 @ X32))),
% 0.39/0.60      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.39/0.60            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.39/0.60          | ~ (l1_orders_2 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.60  thf(t27_yellow_1, conjecture,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( l1_orders_2 @ A ) =>
% 0.39/0.60       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.39/0.60         ( g1_orders_2 @
% 0.39/0.60           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.39/0.60           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i]:
% 0.39/0.60        ( ( l1_orders_2 @ A ) =>
% 0.39/0.60          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.39/0.60            ( g1_orders_2 @
% 0.39/0.60              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.39/0.60              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.39/0.60         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.39/0.60             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(redefinition_k6_partfun1, axiom,
% 0.39/0.60    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.39/0.60  thf('8', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.39/0.60         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.39/0.60             (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.39/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.60  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.39/0.60  thf('11', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.39/0.60  thf(dt_k6_partfun1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( m1_subset_1 @
% 0.39/0.60         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.39/0.60       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.39/0.60  thf('13', plain, (![X28 : $i]: (v1_partfun1 @ (k6_partfun1 @ X28) @ X28)),
% 0.39/0.60      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.39/0.60  thf('14', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.39/0.60  thf('15', plain, (![X28 : $i]: (v1_partfun1 @ (k6_relat_1 @ X28) @ X28)),
% 0.39/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.60  thf('16', plain,
% 0.39/0.60      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['12', '15'])).
% 0.39/0.60  thf(t26_yellow_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.39/0.60         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.39/0.60         ( v1_yellow_1 @ A ) ) =>
% 0.39/0.60       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.39/0.60         ( g1_orders_2 @
% 0.39/0.60           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.39/0.60           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      (![X38 : $i]:
% 0.39/0.60         (((k5_yellow_1 @ k1_xboole_0 @ X38)
% 0.39/0.60            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.39/0.60               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.39/0.60          | ~ (v1_yellow_1 @ X38)
% 0.39/0.60          | ~ (v1_partfun1 @ X38 @ k1_xboole_0)
% 0.39/0.60          | ~ (v1_funct_1 @ X38)
% 0.39/0.60          | ~ (v4_relat_1 @ X38 @ k1_xboole_0)
% 0.39/0.60          | ~ (v1_relat_1 @ X38))),
% 0.39/0.60      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.39/0.60  thf('18', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.39/0.60  thf('19', plain,
% 0.39/0.60      (![X38 : $i]:
% 0.39/0.60         (((k5_yellow_1 @ k1_xboole_0 @ X38)
% 0.39/0.60            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.39/0.60               (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))
% 0.39/0.60          | ~ (v1_yellow_1 @ X38)
% 0.39/0.60          | ~ (v1_partfun1 @ X38 @ k1_xboole_0)
% 0.39/0.60          | ~ (v1_funct_1 @ X38)
% 0.39/0.60          | ~ (v4_relat_1 @ X38 @ k1_xboole_0)
% 0.39/0.60          | ~ (v1_relat_1 @ X38))),
% 0.39/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.60        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.60        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.39/0.60        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.39/0.60        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.39/0.60        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.39/0.60            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.39/0.60               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['16', '19'])).
% 0.39/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.60  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.60  thf('22', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.39/0.60  thf(fc3_funct_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.39/0.60       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.39/0.60  thf('23', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.39/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.60  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.60      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.60  thf(t60_relat_1, axiom,
% 0.39/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.39/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.60  thf('25', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.39/0.60  thf(d18_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.60  thf('26', plain,
% 0.39/0.60      (![X24 : $i, X25 : $i]:
% 0.39/0.60         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.39/0.60          | (v4_relat_1 @ X24 @ X25)
% 0.39/0.60          | ~ (v1_relat_1 @ X24))),
% 0.39/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.39/0.60  thf('27', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.39/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.60          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.60  thf('28', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.39/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.60  thf('29', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.60      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.60  thf('30', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.39/0.60      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.39/0.60  thf('31', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.39/0.60  thf('32', plain, (![X27 : $i]: (v1_funct_1 @ (k6_relat_1 @ X27))),
% 0.39/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.39/0.60  thf('33', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.39/0.60      inference('sup+', [status(thm)], ['31', '32'])).
% 0.39/0.60  thf(rc4_orders_2, axiom,
% 0.39/0.60    (?[A:$i]:
% 0.39/0.60     ( ( v1_orders_2 @ A ) & ( v2_struct_0 @ A ) & ( l1_orders_2 @ A ) ))).
% 0.39/0.60  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.39/0.60      inference('cnf', [status(esa)], [rc4_orders_2])).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.60  thf(fc10_yellow_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.39/0.60  thf('36', plain,
% 0.39/0.60      (![X33 : $i, X34 : $i]:
% 0.39/0.60         ((v1_yellow_1 @ (k2_funcop_1 @ X33 @ X34)) | ~ (l1_orders_2 @ X34))),
% 0.39/0.60      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.39/0.60  thf('37', plain,
% 0.39/0.60      (![X36 : $i, X37 : $i]:
% 0.39/0.60         ((k7_funcop_1 @ X36 @ X37) = (k2_funcop_1 @ X36 @ X37))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.39/0.60  thf('38', plain,
% 0.39/0.60      (![X33 : $i, X34 : $i]:
% 0.39/0.60         ((v1_yellow_1 @ (k7_funcop_1 @ X33 @ X34)) | ~ (l1_orders_2 @ X34))),
% 0.39/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.39/0.60  thf('39', plain,
% 0.39/0.60      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['35', '38'])).
% 0.39/0.60  thf('40', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.39/0.60      inference('sup-', [status(thm)], ['34', '39'])).
% 0.39/0.60  thf('41', plain,
% 0.39/0.60      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.39/0.60         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.39/0.60            (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.39/0.60      inference('demod', [status(thm)], ['20', '21', '24', '30', '33', '40'])).
% 0.39/0.60  thf('42', plain,
% 0.39/0.60      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.39/0.60         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['9', '41'])).
% 0.39/0.60  thf('43', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.39/0.60            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.39/0.60          | ~ (l1_orders_2 @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['6', '42'])).
% 0.39/0.60  thf('44', plain, (~ (l1_orders_2 @ sk_A_1)),
% 0.39/0.60      inference('eq_res', [status(thm)], ['43'])).
% 0.39/0.60  thf('45', plain, ((l1_orders_2 @ sk_A_1)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('46', plain, ($false), inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
