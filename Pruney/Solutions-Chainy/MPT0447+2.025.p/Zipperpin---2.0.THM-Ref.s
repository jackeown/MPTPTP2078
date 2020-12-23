%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tDe9sUqdgU

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:56 EST 2020

% Result     : Theorem 34.13s
% Output     : Refutation 34.13s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 690 expanded)
%              Number of leaves         :   42 ( 249 expanded)
%              Depth                    :   24
%              Number of atoms          : 1513 (5502 expanded)
%              Number of equality atoms :   83 ( 347 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_tarski_type,type,(
    r2_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k2_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('11',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k3_tarski @ ( k2_tarski @ X13 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k3_tarski @ ( k2_tarski @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k3_tarski @ ( k2_tarski @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('16',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ k1_xboole_0 ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('31',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ k1_xboole_0 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('35',plain,
    ( sk_B_1
    = ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','28','33','34'])).

thf(t13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X58 @ X57 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X58 ) @ ( k1_relat_1 @ X57 ) ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf('37',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_relat_1 @ X57 )
      | ( ( k1_relat_1 @ ( k3_tarski @ ( k2_tarski @ X58 @ X57 ) ) )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X58 ) @ ( k1_relat_1 @ X57 ) ) ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X14: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ k1_xboole_0 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('56',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('58',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) )
    = ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('61',plain,
    ( ( k3_relat_1 @ sk_B_1 )
    = ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('63',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('64',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['61','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('73',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X59 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X60 ) @ ( k2_relat_1 @ X59 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X60 @ X59 ) ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('74',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('75',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('76',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X59 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X60 ) @ ( k2_relat_1 @ X59 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X60 @ X59 ) ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ( ( k2_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('80',plain,(
    ! [X51: $i,X54: $i] :
      ( ( X54
        = ( k2_relat_1 @ X51 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X54 @ X51 ) @ ( sk_C_3 @ X54 @ X51 ) ) @ X51 )
      | ( r2_hidden @ ( sk_C_3 @ X54 @ X51 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('81',plain,(
    ! [X29: $i] :
      ( r1_xboole_0 @ X29 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t136_zfmisc_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ~ ( ( r1_tarski @ C @ B )
            & ~ ( r2_tarski @ C @ B )
            & ~ ( r2_hidden @ C @ B ) )
      & ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ ( k1_zfmisc_1 @ C ) @ B ) )
      & ! [C: $i,D: $i] :
          ( ( ( r2_hidden @ C @ B )
            & ( r1_tarski @ D @ C ) )
         => ( r2_hidden @ D @ B ) )
      & ( r2_hidden @ A @ B ) ) )).

thf('82',plain,(
    ! [X39: $i] :
      ( r2_hidden @ X39 @ ( sk_B @ X39 ) ) ),
    inference(cnf,[status(esa)],[t136_zfmisc_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('83',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_B @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('88',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X18: $i] :
      ( r1_tarski @ k1_xboole_0 @ X18 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','21'])).

thf('91',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('92',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['79','88','89','90','91','92','93'])).

thf('95',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('96',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) )
    = ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('99',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','102'])).

thf('104',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('105',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('106',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','108'])).

thf('110',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('116',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ( r1_tarski @ ( k2_xboole_0 @ X32 @ X34 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('117',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('118',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X32 @ X34 ) ) @ X33 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) @ ( k3_relat_1 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ ( k4_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['114','119'])).

thf('121',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('122',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k3_tarski @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('124',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('125',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k3_tarski @ ( k2_tarski @ X13 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k3_tarski @ ( k2_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_tarski @ ( k2_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['123','130'])).

thf('132',plain,(
    ! [X56: $i] :
      ( ( ( k3_relat_1 @ X56 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('133',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('134',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k3_tarski @ ( k2_tarski @ X13 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','135'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('137',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('138',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('142',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X32 @ X34 ) ) @ X33 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X0 ) @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X0 ) @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ) @ ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['131','145'])).

thf('147',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('149',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('152',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('154',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('156',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_A ) @ k1_xboole_0 ) )
    = ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X36 @ X35 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('159',plain,
    ( ( k3_relat_1 @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['120','121','122','159'])).

thf('161',plain,(
    $false ),
    inference(demod,[status(thm)],['0','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tDe9sUqdgU
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 34.13/34.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 34.13/34.39  % Solved by: fo/fo7.sh
% 34.13/34.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 34.13/34.39  % done 41744 iterations in 33.902s
% 34.13/34.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 34.13/34.39  % SZS output start Refutation
% 34.13/34.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 34.13/34.39  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 34.13/34.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 34.13/34.39  thf(sk_B_type, type, sk_B: $i > $i).
% 34.13/34.39  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 34.13/34.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 34.13/34.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 34.13/34.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 34.13/34.39  thf(sk_B_1_type, type, sk_B_1: $i).
% 34.13/34.39  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 34.13/34.39  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 34.13/34.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 34.13/34.39  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 34.13/34.39  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 34.13/34.39  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 34.13/34.39  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 34.13/34.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 34.13/34.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 34.13/34.39  thf(r2_tarski_type, type, r2_tarski: $i > $i > $o).
% 34.13/34.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 34.13/34.39  thf(sk_A_type, type, sk_A: $i).
% 34.13/34.39  thf(t31_relat_1, conjecture,
% 34.13/34.39    (![A:$i]:
% 34.13/34.39     ( ( v1_relat_1 @ A ) =>
% 34.13/34.39       ( ![B:$i]:
% 34.13/34.39         ( ( v1_relat_1 @ B ) =>
% 34.13/34.39           ( ( r1_tarski @ A @ B ) =>
% 34.13/34.39             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 34.13/34.39  thf(zf_stmt_0, negated_conjecture,
% 34.13/34.39    (~( ![A:$i]:
% 34.13/34.39        ( ( v1_relat_1 @ A ) =>
% 34.13/34.39          ( ![B:$i]:
% 34.13/34.39            ( ( v1_relat_1 @ B ) =>
% 34.13/34.39              ( ( r1_tarski @ A @ B ) =>
% 34.13/34.39                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 34.13/34.39    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 34.13/34.39  thf('0', plain,
% 34.13/34.39      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 34.13/34.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.13/34.39  thf(d6_relat_1, axiom,
% 34.13/34.39    (![A:$i]:
% 34.13/34.39     ( ( v1_relat_1 @ A ) =>
% 34.13/34.39       ( ( k3_relat_1 @ A ) =
% 34.13/34.39         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 34.13/34.39  thf('1', plain,
% 34.13/34.39      (![X56 : $i]:
% 34.13/34.39         (((k3_relat_1 @ X56)
% 34.13/34.39            = (k2_xboole_0 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56)))
% 34.13/34.39          | ~ (v1_relat_1 @ X56))),
% 34.13/34.39      inference('cnf', [status(esa)], [d6_relat_1])).
% 34.13/34.39  thf(l51_zfmisc_1, axiom,
% 34.13/34.39    (![A:$i,B:$i]:
% 34.13/34.39     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 34.13/34.39  thf('2', plain,
% 34.13/34.39      (![X37 : $i, X38 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.13/34.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.13/34.39  thf('3', plain,
% 34.13/34.39      (![X56 : $i]:
% 34.13/34.39         (((k3_relat_1 @ X56)
% 34.13/34.39            = (k3_tarski @ 
% 34.13/34.39               (k2_tarski @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 34.13/34.39          | ~ (v1_relat_1 @ X56))),
% 34.13/34.39      inference('demod', [status(thm)], ['1', '2'])).
% 34.13/34.39  thf(t7_xboole_1, axiom,
% 34.13/34.39    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 34.13/34.39  thf('4', plain,
% 34.13/34.39      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 34.13/34.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 34.13/34.39  thf('5', plain,
% 34.13/34.39      (![X37 : $i, X38 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.13/34.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.13/34.39  thf('6', plain,
% 34.13/34.39      (![X30 : $i, X31 : $i]:
% 34.13/34.39         (r1_tarski @ X30 @ (k3_tarski @ (k2_tarski @ X30 @ X31)))),
% 34.13/34.39      inference('demod', [status(thm)], ['4', '5'])).
% 34.13/34.39  thf('7', plain,
% 34.13/34.39      (![X0 : $i]:
% 34.13/34.39         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 34.13/34.39          | ~ (v1_relat_1 @ X0))),
% 34.13/34.39      inference('sup+', [status(thm)], ['3', '6'])).
% 34.13/34.39  thf(commutativity_k2_tarski, axiom,
% 34.13/34.39    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 34.13/34.39  thf('8', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf('9', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 34.13/34.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.13/34.39  thf(t10_xboole_1, axiom,
% 34.13/34.39    (![A:$i,B:$i,C:$i]:
% 34.13/34.39     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 34.13/34.39  thf('10', plain,
% 34.13/34.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X11 @ X12)
% 34.13/34.39          | (r1_tarski @ X11 @ (k2_xboole_0 @ X13 @ X12)))),
% 34.13/34.39      inference('cnf', [status(esa)], [t10_xboole_1])).
% 34.13/34.39  thf('11', plain,
% 34.13/34.39      (![X37 : $i, X38 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.13/34.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.13/34.39  thf('12', plain,
% 34.13/34.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X11 @ X12)
% 34.13/34.39          | (r1_tarski @ X11 @ (k3_tarski @ (k2_tarski @ X13 @ X12))))),
% 34.13/34.39      inference('demod', [status(thm)], ['10', '11'])).
% 34.13/34.39  thf('13', plain,
% 34.13/34.39      (![X0 : $i]: (r1_tarski @ sk_A @ (k3_tarski @ (k2_tarski @ X0 @ sk_B_1)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['9', '12'])).
% 34.13/34.39  thf('14', plain,
% 34.13/34.39      (![X0 : $i]: (r1_tarski @ sk_A @ (k3_tarski @ (k2_tarski @ sk_B_1 @ X0)))),
% 34.13/34.39      inference('sup+', [status(thm)], ['8', '13'])).
% 34.13/34.39  thf(t43_xboole_1, axiom,
% 34.13/34.39    (![A:$i,B:$i,C:$i]:
% 34.13/34.39     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 34.13/34.39       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 34.13/34.39  thf('15', plain,
% 34.13/34.39      (![X23 : $i, X24 : $i, X25 : $i]:
% 34.13/34.39         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 34.13/34.39          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 34.13/34.39      inference('cnf', [status(esa)], [t43_xboole_1])).
% 34.13/34.39  thf('16', plain,
% 34.13/34.39      (![X37 : $i, X38 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.13/34.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.13/34.39  thf('17', plain,
% 34.13/34.39      (![X23 : $i, X24 : $i, X25 : $i]:
% 34.13/34.39         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 34.13/34.39          | ~ (r1_tarski @ X23 @ (k3_tarski @ (k2_tarski @ X24 @ X25))))),
% 34.13/34.39      inference('demod', [status(thm)], ['15', '16'])).
% 34.13/34.39  thf('18', plain,
% 34.13/34.39      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B_1) @ X0)),
% 34.13/34.39      inference('sup-', [status(thm)], ['14', '17'])).
% 34.13/34.39  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 34.13/34.39  thf('19', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 34.13/34.39      inference('cnf', [status(esa)], [t2_xboole_1])).
% 34.13/34.39  thf(d10_xboole_0, axiom,
% 34.13/34.39    (![A:$i,B:$i]:
% 34.13/34.39     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 34.13/34.39  thf('20', plain,
% 34.13/34.39      (![X8 : $i, X10 : $i]:
% 34.13/34.39         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 34.13/34.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 34.13/34.39  thf('21', plain,
% 34.13/34.39      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['19', '20'])).
% 34.13/34.39  thf('22', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['18', '21'])).
% 34.13/34.39  thf(t39_xboole_1, axiom,
% 34.13/34.39    (![A:$i,B:$i]:
% 34.13/34.39     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 34.13/34.39  thf('23', plain,
% 34.13/34.39      (![X21 : $i, X22 : $i]:
% 34.13/34.39         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 34.13/34.39           = (k2_xboole_0 @ X21 @ X22))),
% 34.13/34.39      inference('cnf', [status(esa)], [t39_xboole_1])).
% 34.13/34.39  thf('24', plain,
% 34.13/34.39      (![X37 : $i, X38 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.13/34.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.13/34.39  thf('25', plain,
% 34.13/34.39      (![X37 : $i, X38 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.13/34.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.13/34.39  thf('26', plain,
% 34.13/34.39      (![X21 : $i, X22 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X21 @ (k4_xboole_0 @ X22 @ X21)))
% 34.13/34.39           = (k3_tarski @ (k2_tarski @ X21 @ X22)))),
% 34.13/34.39      inference('demod', [status(thm)], ['23', '24', '25'])).
% 34.13/34.39  thf('27', plain,
% 34.13/34.39      (((k3_tarski @ (k2_tarski @ sk_B_1 @ k1_xboole_0))
% 34.13/34.39         = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_A)))),
% 34.13/34.39      inference('sup+', [status(thm)], ['22', '26'])).
% 34.13/34.39  thf('28', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf('29', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf(t1_boole, axiom,
% 34.13/34.39    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 34.13/34.39  thf('30', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 34.13/34.39      inference('cnf', [status(esa)], [t1_boole])).
% 34.13/34.39  thf('31', plain,
% 34.13/34.39      (![X37 : $i, X38 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.13/34.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.13/34.39  thf('32', plain,
% 34.13/34.39      (![X14 : $i]: ((k3_tarski @ (k2_tarski @ X14 @ k1_xboole_0)) = (X14))),
% 34.13/34.39      inference('demod', [status(thm)], ['30', '31'])).
% 34.13/34.39  thf('33', plain,
% 34.13/34.39      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 34.13/34.39      inference('sup+', [status(thm)], ['29', '32'])).
% 34.13/34.39  thf('34', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf('35', plain, (((sk_B_1) = (k3_tarski @ (k2_tarski @ sk_A @ sk_B_1)))),
% 34.13/34.39      inference('demod', [status(thm)], ['27', '28', '33', '34'])).
% 34.13/34.39  thf(t13_relat_1, axiom,
% 34.13/34.39    (![A:$i]:
% 34.13/34.39     ( ( v1_relat_1 @ A ) =>
% 34.13/34.39       ( ![B:$i]:
% 34.13/34.39         ( ( v1_relat_1 @ B ) =>
% 34.13/34.39           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 34.13/34.39             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 34.13/34.39  thf('36', plain,
% 34.13/34.39      (![X57 : $i, X58 : $i]:
% 34.13/34.39         (~ (v1_relat_1 @ X57)
% 34.13/34.39          | ((k1_relat_1 @ (k2_xboole_0 @ X58 @ X57))
% 34.13/34.39              = (k2_xboole_0 @ (k1_relat_1 @ X58) @ (k1_relat_1 @ X57)))
% 34.13/34.39          | ~ (v1_relat_1 @ X58))),
% 34.13/34.39      inference('cnf', [status(esa)], [t13_relat_1])).
% 34.13/34.39  thf('37', plain,
% 34.13/34.39      (![X37 : $i, X38 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.13/34.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.13/34.39  thf('38', plain,
% 34.13/34.39      (![X37 : $i, X38 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.13/34.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.13/34.39  thf('39', plain,
% 34.13/34.39      (![X57 : $i, X58 : $i]:
% 34.13/34.39         (~ (v1_relat_1 @ X57)
% 34.13/34.39          | ((k1_relat_1 @ (k3_tarski @ (k2_tarski @ X58 @ X57)))
% 34.13/34.39              = (k3_tarski @ 
% 34.13/34.39                 (k2_tarski @ (k1_relat_1 @ X58) @ (k1_relat_1 @ X57))))
% 34.13/34.39          | ~ (v1_relat_1 @ X58))),
% 34.13/34.39      inference('demod', [status(thm)], ['36', '37', '38'])).
% 34.13/34.39  thf('40', plain,
% 34.13/34.39      (![X30 : $i, X31 : $i]:
% 34.13/34.39         (r1_tarski @ X30 @ (k3_tarski @ (k2_tarski @ X30 @ X31)))),
% 34.13/34.39      inference('demod', [status(thm)], ['4', '5'])).
% 34.13/34.39  thf(t1_xboole_1, axiom,
% 34.13/34.39    (![A:$i,B:$i,C:$i]:
% 34.13/34.39     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 34.13/34.39       ( r1_tarski @ A @ C ) ))).
% 34.13/34.39  thf('41', plain,
% 34.13/34.39      (![X15 : $i, X16 : $i, X17 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X15 @ X16)
% 34.13/34.39          | ~ (r1_tarski @ X16 @ X17)
% 34.13/34.39          | (r1_tarski @ X15 @ X17))),
% 34.13/34.39      inference('cnf', [status(esa)], [t1_xboole_1])).
% 34.13/34.39  thf('42', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.13/34.39         ((r1_tarski @ X1 @ X2)
% 34.13/34.39          | ~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2))),
% 34.13/34.39      inference('sup-', [status(thm)], ['40', '41'])).
% 34.13/34.39  thf('43', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.13/34.39         (~ (r1_tarski @ (k1_relat_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0))) @ 
% 34.13/34.39             X2)
% 34.13/34.39          | ~ (v1_relat_1 @ X1)
% 34.13/34.39          | ~ (v1_relat_1 @ X0)
% 34.13/34.39          | (r1_tarski @ (k1_relat_1 @ X1) @ X2))),
% 34.13/34.39      inference('sup-', [status(thm)], ['39', '42'])).
% 34.13/34.39  thf('44', plain,
% 34.13/34.39      (![X0 : $i]:
% 34.13/34.39         (~ (r1_tarski @ (k1_relat_1 @ sk_B_1) @ X0)
% 34.13/34.39          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 34.13/34.39          | ~ (v1_relat_1 @ sk_B_1)
% 34.13/34.39          | ~ (v1_relat_1 @ sk_A))),
% 34.13/34.39      inference('sup-', [status(thm)], ['35', '43'])).
% 34.13/34.39  thf('45', plain, ((v1_relat_1 @ sk_B_1)),
% 34.13/34.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.13/34.39  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 34.13/34.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.13/34.39  thf('47', plain,
% 34.13/34.39      (![X0 : $i]:
% 34.13/34.39         (~ (r1_tarski @ (k1_relat_1 @ sk_B_1) @ X0)
% 34.13/34.39          | (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 34.13/34.39      inference('demod', [status(thm)], ['44', '45', '46'])).
% 34.13/34.39  thf('48', plain,
% 34.13/34.39      ((~ (v1_relat_1 @ sk_B_1)
% 34.13/34.39        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['7', '47'])).
% 34.13/34.39  thf('49', plain, ((v1_relat_1 @ sk_B_1)),
% 34.13/34.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.13/34.39  thf('50', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 34.13/34.39      inference('demod', [status(thm)], ['48', '49'])).
% 34.13/34.39  thf('51', plain,
% 34.13/34.39      (![X14 : $i]: ((k3_tarski @ (k2_tarski @ X14 @ k1_xboole_0)) = (X14))),
% 34.13/34.39      inference('demod', [status(thm)], ['30', '31'])).
% 34.13/34.39  thf('52', plain,
% 34.13/34.39      (![X23 : $i, X24 : $i, X25 : $i]:
% 34.13/34.39         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 34.13/34.39          | ~ (r1_tarski @ X23 @ (k3_tarski @ (k2_tarski @ X24 @ X25))))),
% 34.13/34.39      inference('demod', [status(thm)], ['15', '16'])).
% 34.13/34.39  thf('53', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X1 @ X0)
% 34.13/34.39          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['51', '52'])).
% 34.13/34.39  thf('54', plain,
% 34.13/34.39      ((r1_tarski @ 
% 34.13/34.39        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1)) @ 
% 34.13/34.39        k1_xboole_0)),
% 34.13/34.39      inference('sup-', [status(thm)], ['50', '53'])).
% 34.13/34.39  thf('55', plain,
% 34.13/34.39      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['19', '20'])).
% 34.13/34.39  thf('56', plain,
% 34.13/34.39      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 34.13/34.39         = (k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['54', '55'])).
% 34.13/34.39  thf('57', plain,
% 34.13/34.39      (![X21 : $i, X22 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X21 @ (k4_xboole_0 @ X22 @ X21)))
% 34.13/34.39           = (k3_tarski @ (k2_tarski @ X21 @ X22)))),
% 34.13/34.39      inference('demod', [status(thm)], ['23', '24', '25'])).
% 34.13/34.39  thf('58', plain,
% 34.13/34.39      (((k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_1) @ k1_xboole_0))
% 34.13/34.39         = (k3_tarski @ 
% 34.13/34.39            (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))))),
% 34.13/34.39      inference('sup+', [status(thm)], ['56', '57'])).
% 34.13/34.39  thf('59', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf('60', plain,
% 34.13/34.39      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 34.13/34.39      inference('sup+', [status(thm)], ['29', '32'])).
% 34.13/34.39  thf('61', plain,
% 34.13/34.39      (((k3_relat_1 @ sk_B_1)
% 34.13/34.39         = (k3_tarski @ 
% 34.13/34.39            (k2_tarski @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A))))),
% 34.13/34.39      inference('demod', [status(thm)], ['58', '59', '60'])).
% 34.13/34.39  thf('62', plain,
% 34.13/34.39      (![X30 : $i, X31 : $i]:
% 34.13/34.39         (r1_tarski @ X30 @ (k3_tarski @ (k2_tarski @ X30 @ X31)))),
% 34.13/34.39      inference('demod', [status(thm)], ['4', '5'])).
% 34.13/34.39  thf('63', plain,
% 34.13/34.39      (![X56 : $i]:
% 34.13/34.39         (((k3_relat_1 @ X56)
% 34.13/34.39            = (k3_tarski @ 
% 34.13/34.39               (k2_tarski @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 34.13/34.39          | ~ (v1_relat_1 @ X56))),
% 34.13/34.39      inference('demod', [status(thm)], ['1', '2'])).
% 34.13/34.39  thf('64', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf('65', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.13/34.39         ((r1_tarski @ X1 @ X2)
% 34.13/34.39          | ~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2))),
% 34.13/34.39      inference('sup-', [status(thm)], ['40', '41'])).
% 34.13/34.39  thf('66', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.13/34.39         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2)
% 34.13/34.39          | (r1_tarski @ X0 @ X2))),
% 34.13/34.39      inference('sup-', [status(thm)], ['64', '65'])).
% 34.13/34.39  thf('67', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 34.13/34.39          | ~ (v1_relat_1 @ X0)
% 34.13/34.39          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 34.13/34.39      inference('sup-', [status(thm)], ['63', '66'])).
% 34.13/34.39  thf('68', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         ((r1_tarski @ (k2_relat_1 @ X1) @ 
% 34.13/34.39           (k3_tarski @ (k2_tarski @ (k3_relat_1 @ X1) @ X0)))
% 34.13/34.39          | ~ (v1_relat_1 @ X1))),
% 34.13/34.39      inference('sup-', [status(thm)], ['62', '67'])).
% 34.13/34.39  thf('69', plain,
% 34.13/34.39      (((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))
% 34.13/34.39        | ~ (v1_relat_1 @ sk_B_1))),
% 34.13/34.39      inference('sup+', [status(thm)], ['61', '68'])).
% 34.13/34.39  thf('70', plain, ((v1_relat_1 @ sk_B_1)),
% 34.13/34.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.13/34.39  thf('71', plain,
% 34.13/34.39      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 34.13/34.39      inference('demod', [status(thm)], ['69', '70'])).
% 34.13/34.39  thf('72', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['18', '21'])).
% 34.13/34.39  thf(t28_relat_1, axiom,
% 34.13/34.39    (![A:$i]:
% 34.13/34.39     ( ( v1_relat_1 @ A ) =>
% 34.13/34.39       ( ![B:$i]:
% 34.13/34.39         ( ( v1_relat_1 @ B ) =>
% 34.13/34.39           ( r1_tarski @
% 34.13/34.39             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 34.13/34.39             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 34.13/34.39  thf('73', plain,
% 34.13/34.39      (![X59 : $i, X60 : $i]:
% 34.13/34.39         (~ (v1_relat_1 @ X59)
% 34.13/34.39          | (r1_tarski @ 
% 34.13/34.39             (k6_subset_1 @ (k2_relat_1 @ X60) @ (k2_relat_1 @ X59)) @ 
% 34.13/34.39             (k2_relat_1 @ (k6_subset_1 @ X60 @ X59)))
% 34.13/34.39          | ~ (v1_relat_1 @ X60))),
% 34.13/34.39      inference('cnf', [status(esa)], [t28_relat_1])).
% 34.13/34.39  thf(redefinition_k6_subset_1, axiom,
% 34.13/34.39    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 34.13/34.39  thf('74', plain,
% 34.13/34.39      (![X47 : $i, X48 : $i]:
% 34.13/34.39         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 34.13/34.39      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 34.13/34.39  thf('75', plain,
% 34.13/34.39      (![X47 : $i, X48 : $i]:
% 34.13/34.39         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 34.13/34.39      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 34.13/34.39  thf('76', plain,
% 34.13/34.39      (![X59 : $i, X60 : $i]:
% 34.13/34.39         (~ (v1_relat_1 @ X59)
% 34.13/34.39          | (r1_tarski @ 
% 34.13/34.39             (k4_xboole_0 @ (k2_relat_1 @ X60) @ (k2_relat_1 @ X59)) @ 
% 34.13/34.39             (k2_relat_1 @ (k4_xboole_0 @ X60 @ X59)))
% 34.13/34.39          | ~ (v1_relat_1 @ X60))),
% 34.13/34.39      inference('demod', [status(thm)], ['73', '74', '75'])).
% 34.13/34.39  thf('77', plain,
% 34.13/34.39      (![X8 : $i, X10 : $i]:
% 34.13/34.39         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 34.13/34.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 34.13/34.39  thf('78', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (~ (v1_relat_1 @ X1)
% 34.13/34.39          | ~ (v1_relat_1 @ X0)
% 34.13/34.39          | ~ (r1_tarski @ (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 34.13/34.39               (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 34.13/34.39          | ((k2_relat_1 @ (k4_xboole_0 @ X1 @ X0))
% 34.13/34.39              = (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))),
% 34.13/34.39      inference('sup-', [status(thm)], ['76', '77'])).
% 34.13/34.39  thf('79', plain,
% 34.13/34.39      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 34.13/34.39           (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 34.13/34.39        | ((k2_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 34.13/34.39            = (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))
% 34.13/34.39        | ~ (v1_relat_1 @ sk_B_1)
% 34.13/34.39        | ~ (v1_relat_1 @ sk_A))),
% 34.13/34.39      inference('sup-', [status(thm)], ['72', '78'])).
% 34.13/34.39  thf(d5_relat_1, axiom,
% 34.13/34.39    (![A:$i,B:$i]:
% 34.13/34.39     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 34.13/34.39       ( ![C:$i]:
% 34.13/34.39         ( ( r2_hidden @ C @ B ) <=>
% 34.13/34.39           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 34.13/34.39  thf('80', plain,
% 34.13/34.39      (![X51 : $i, X54 : $i]:
% 34.13/34.39         (((X54) = (k2_relat_1 @ X51))
% 34.13/34.39          | (r2_hidden @ 
% 34.13/34.39             (k4_tarski @ (sk_D @ X54 @ X51) @ (sk_C_3 @ X54 @ X51)) @ X51)
% 34.13/34.39          | (r2_hidden @ (sk_C_3 @ X54 @ X51) @ X54))),
% 34.13/34.39      inference('cnf', [status(esa)], [d5_relat_1])).
% 34.13/34.39  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 34.13/34.39  thf('81', plain, (![X29 : $i]: (r1_xboole_0 @ X29 @ k1_xboole_0)),
% 34.13/34.39      inference('cnf', [status(esa)], [t65_xboole_1])).
% 34.13/34.39  thf(t136_zfmisc_1, axiom,
% 34.13/34.39    (![A:$i]:
% 34.13/34.39     ( ?[B:$i]:
% 34.13/34.39       ( ( ![C:$i]:
% 34.13/34.39           ( ~( ( r1_tarski @ C @ B ) & ( ~( r2_tarski @ C @ B ) ) & 
% 34.13/34.39                ( ~( r2_hidden @ C @ B ) ) ) ) ) & 
% 34.13/34.39         ( ![C:$i]:
% 34.13/34.39           ( ( r2_hidden @ C @ B ) => ( r2_hidden @ ( k1_zfmisc_1 @ C ) @ B ) ) ) & 
% 34.13/34.39         ( ![C:$i,D:$i]:
% 34.13/34.39           ( ( ( r2_hidden @ C @ B ) & ( r1_tarski @ D @ C ) ) =>
% 34.13/34.39             ( r2_hidden @ D @ B ) ) ) & 
% 34.13/34.39         ( r2_hidden @ A @ B ) ) ))).
% 34.13/34.39  thf('82', plain, (![X39 : $i]: (r2_hidden @ X39 @ (sk_B @ X39))),
% 34.13/34.39      inference('cnf', [status(esa)], [t136_zfmisc_1])).
% 34.13/34.39  thf(t3_xboole_0, axiom,
% 34.13/34.39    (![A:$i,B:$i]:
% 34.13/34.39     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 34.13/34.39            ( r1_xboole_0 @ A @ B ) ) ) & 
% 34.13/34.39       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 34.13/34.39            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 34.13/34.39  thf('83', plain,
% 34.13/34.39      (![X4 : $i, X6 : $i, X7 : $i]:
% 34.13/34.39         (~ (r2_hidden @ X6 @ X4)
% 34.13/34.39          | ~ (r2_hidden @ X6 @ X7)
% 34.13/34.39          | ~ (r1_xboole_0 @ X4 @ X7))),
% 34.13/34.39      inference('cnf', [status(esa)], [t3_xboole_0])).
% 34.13/34.39  thf('84', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (~ (r1_xboole_0 @ (sk_B @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 34.13/34.39      inference('sup-', [status(thm)], ['82', '83'])).
% 34.13/34.39  thf('85', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 34.13/34.39      inference('sup-', [status(thm)], ['81', '84'])).
% 34.13/34.39  thf('86', plain,
% 34.13/34.39      (![X0 : $i]:
% 34.13/34.39         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 34.13/34.39          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['80', '85'])).
% 34.13/34.39  thf('87', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 34.13/34.39      inference('sup-', [status(thm)], ['81', '84'])).
% 34.13/34.39  thf('88', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['86', '87'])).
% 34.13/34.39  thf('89', plain, (![X18 : $i]: (r1_tarski @ k1_xboole_0 @ X18)),
% 34.13/34.39      inference('cnf', [status(esa)], [t2_xboole_1])).
% 34.13/34.39  thf('90', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['18', '21'])).
% 34.13/34.39  thf('91', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['86', '87'])).
% 34.13/34.39  thf('92', plain, ((v1_relat_1 @ sk_B_1)),
% 34.13/34.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.13/34.39  thf('93', plain, ((v1_relat_1 @ sk_A)),
% 34.13/34.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.13/34.39  thf('94', plain,
% 34.13/34.39      (((k1_xboole_0)
% 34.13/34.39         = (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1)))),
% 34.13/34.39      inference('demod', [status(thm)],
% 34.13/34.39                ['79', '88', '89', '90', '91', '92', '93'])).
% 34.13/34.39  thf('95', plain,
% 34.13/34.39      (![X21 : $i, X22 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X21 @ (k4_xboole_0 @ X22 @ X21)))
% 34.13/34.39           = (k3_tarski @ (k2_tarski @ X21 @ X22)))),
% 34.13/34.39      inference('demod', [status(thm)], ['23', '24', '25'])).
% 34.13/34.39  thf('96', plain,
% 34.13/34.39      (((k3_tarski @ (k2_tarski @ (k2_relat_1 @ sk_B_1) @ k1_xboole_0))
% 34.13/34.39         = (k3_tarski @ 
% 34.13/34.39            (k2_tarski @ (k2_relat_1 @ sk_B_1) @ (k2_relat_1 @ sk_A))))),
% 34.13/34.39      inference('sup+', [status(thm)], ['94', '95'])).
% 34.13/34.39  thf('97', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf('98', plain,
% 34.13/34.39      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 34.13/34.39      inference('sup+', [status(thm)], ['29', '32'])).
% 34.13/34.39  thf('99', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf('100', plain,
% 34.13/34.39      (((k2_relat_1 @ sk_B_1)
% 34.13/34.39         = (k3_tarski @ 
% 34.13/34.39            (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))))),
% 34.13/34.39      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 34.13/34.39  thf('101', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.13/34.39         ((r1_tarski @ X1 @ X2)
% 34.13/34.39          | ~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2))),
% 34.13/34.39      inference('sup-', [status(thm)], ['40', '41'])).
% 34.13/34.39  thf('102', plain,
% 34.13/34.39      (![X0 : $i]:
% 34.13/34.39         (~ (r1_tarski @ (k2_relat_1 @ sk_B_1) @ X0)
% 34.13/34.39          | (r1_tarski @ (k2_relat_1 @ sk_A) @ X0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['100', '101'])).
% 34.13/34.39  thf('103', plain,
% 34.13/34.39      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 34.13/34.39      inference('sup-', [status(thm)], ['71', '102'])).
% 34.13/34.39  thf('104', plain,
% 34.13/34.39      (![X56 : $i]:
% 34.13/34.39         (((k3_relat_1 @ X56)
% 34.13/34.39            = (k3_tarski @ 
% 34.13/34.39               (k2_tarski @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 34.13/34.39          | ~ (v1_relat_1 @ X56))),
% 34.13/34.39      inference('demod', [status(thm)], ['1', '2'])).
% 34.13/34.39  thf('105', plain,
% 34.13/34.39      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 34.13/34.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 34.13/34.39  thf('106', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 34.13/34.39      inference('simplify', [status(thm)], ['105'])).
% 34.13/34.39  thf('107', plain,
% 34.13/34.39      (![X23 : $i, X24 : $i, X25 : $i]:
% 34.13/34.39         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 34.13/34.39          | ~ (r1_tarski @ X23 @ (k3_tarski @ (k2_tarski @ X24 @ X25))))),
% 34.13/34.39      inference('demod', [status(thm)], ['15', '16'])).
% 34.13/34.39  thf('108', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (r1_tarski @ 
% 34.13/34.39          (k4_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1) @ X0)),
% 34.13/34.39      inference('sup-', [status(thm)], ['106', '107'])).
% 34.13/34.39  thf('109', plain,
% 34.13/34.39      (![X0 : $i]:
% 34.13/34.39         ((r1_tarski @ (k4_xboole_0 @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0)) @ 
% 34.13/34.39           (k2_relat_1 @ X0))
% 34.13/34.39          | ~ (v1_relat_1 @ X0))),
% 34.13/34.39      inference('sup+', [status(thm)], ['104', '108'])).
% 34.13/34.39  thf('110', plain,
% 34.13/34.39      (![X15 : $i, X16 : $i, X17 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X15 @ X16)
% 34.13/34.39          | ~ (r1_tarski @ X16 @ X17)
% 34.13/34.39          | (r1_tarski @ X15 @ X17))),
% 34.13/34.39      inference('cnf', [status(esa)], [t1_xboole_1])).
% 34.13/34.39  thf('111', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (~ (v1_relat_1 @ X0)
% 34.13/34.39          | (r1_tarski @ 
% 34.13/34.39             (k4_xboole_0 @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0)) @ X1)
% 34.13/34.39          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 34.13/34.39      inference('sup-', [status(thm)], ['109', '110'])).
% 34.13/34.39  thf('112', plain,
% 34.13/34.39      (((r1_tarski @ 
% 34.13/34.39         (k4_xboole_0 @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 34.13/34.39         (k3_relat_1 @ sk_B_1))
% 34.13/34.39        | ~ (v1_relat_1 @ sk_A))),
% 34.13/34.39      inference('sup-', [status(thm)], ['103', '111'])).
% 34.13/34.39  thf('113', plain, ((v1_relat_1 @ sk_A)),
% 34.13/34.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.13/34.39  thf('114', plain,
% 34.13/34.39      ((r1_tarski @ 
% 34.13/34.39        (k4_xboole_0 @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 34.13/34.39        (k3_relat_1 @ sk_B_1))),
% 34.13/34.39      inference('demod', [status(thm)], ['112', '113'])).
% 34.13/34.39  thf('115', plain,
% 34.13/34.39      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 34.13/34.39      inference('demod', [status(thm)], ['48', '49'])).
% 34.13/34.39  thf(t8_xboole_1, axiom,
% 34.13/34.39    (![A:$i,B:$i,C:$i]:
% 34.13/34.39     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 34.13/34.39       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 34.13/34.39  thf('116', plain,
% 34.13/34.39      (![X32 : $i, X33 : $i, X34 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X32 @ X33)
% 34.13/34.39          | ~ (r1_tarski @ X34 @ X33)
% 34.13/34.39          | (r1_tarski @ (k2_xboole_0 @ X32 @ X34) @ X33))),
% 34.13/34.39      inference('cnf', [status(esa)], [t8_xboole_1])).
% 34.13/34.39  thf('117', plain,
% 34.13/34.39      (![X37 : $i, X38 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 34.13/34.39      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 34.13/34.39  thf('118', plain,
% 34.13/34.39      (![X32 : $i, X33 : $i, X34 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X32 @ X33)
% 34.13/34.39          | ~ (r1_tarski @ X34 @ X33)
% 34.13/34.39          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X32 @ X34)) @ X33))),
% 34.13/34.39      inference('demod', [status(thm)], ['116', '117'])).
% 34.13/34.39  thf('119', plain,
% 34.13/34.39      (![X0 : $i]:
% 34.13/34.39         ((r1_tarski @ (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ X0)) @ 
% 34.13/34.39           (k3_relat_1 @ sk_B_1))
% 34.13/34.39          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['115', '118'])).
% 34.13/34.39  thf('120', plain,
% 34.13/34.39      ((r1_tarski @ 
% 34.13/34.39        (k3_tarski @ 
% 34.13/34.39         (k2_tarski @ (k1_relat_1 @ sk_A) @ 
% 34.13/34.39          (k4_xboole_0 @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)))) @ 
% 34.13/34.39        (k3_relat_1 @ sk_B_1))),
% 34.13/34.39      inference('sup-', [status(thm)], ['114', '119'])).
% 34.13/34.39  thf('121', plain,
% 34.13/34.39      (![X21 : $i, X22 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X21 @ (k4_xboole_0 @ X22 @ X21)))
% 34.13/34.39           = (k3_tarski @ (k2_tarski @ X21 @ X22)))),
% 34.13/34.39      inference('demod', [status(thm)], ['23', '24', '25'])).
% 34.13/34.39  thf('122', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf('123', plain,
% 34.13/34.39      (((k2_relat_1 @ sk_B_1)
% 34.13/34.39         = (k3_tarski @ 
% 34.13/34.39            (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))))),
% 34.13/34.39      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 34.13/34.39  thf('124', plain,
% 34.13/34.39      (![X30 : $i, X31 : $i]:
% 34.13/34.39         (r1_tarski @ X30 @ (k3_tarski @ (k2_tarski @ X30 @ X31)))),
% 34.13/34.39      inference('demod', [status(thm)], ['4', '5'])).
% 34.13/34.39  thf('125', plain,
% 34.13/34.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X11 @ X12)
% 34.13/34.39          | (r1_tarski @ X11 @ (k3_tarski @ (k2_tarski @ X13 @ X12))))),
% 34.13/34.39      inference('demod', [status(thm)], ['10', '11'])).
% 34.13/34.39  thf('126', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.13/34.39         (r1_tarski @ X1 @ 
% 34.13/34.39          (k3_tarski @ (k2_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))))),
% 34.13/34.39      inference('sup-', [status(thm)], ['124', '125'])).
% 34.13/34.39  thf('127', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X1 @ X0)
% 34.13/34.39          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['51', '52'])).
% 34.13/34.39  thf('128', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.13/34.39         (r1_tarski @ 
% 34.13/34.39          (k4_xboole_0 @ X1 @ 
% 34.13/34.39           (k3_tarski @ (k2_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))) @ 
% 34.13/34.39          k1_xboole_0)),
% 34.13/34.39      inference('sup-', [status(thm)], ['126', '127'])).
% 34.13/34.39  thf('129', plain,
% 34.13/34.39      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['19', '20'])).
% 34.13/34.39  thf('130', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.13/34.39         ((k4_xboole_0 @ X1 @ 
% 34.13/34.39           (k3_tarski @ (k2_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))))
% 34.13/34.39           = (k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['128', '129'])).
% 34.13/34.39  thf('131', plain,
% 34.13/34.39      (![X0 : $i]:
% 34.13/34.39         ((k4_xboole_0 @ (k2_relat_1 @ sk_A) @ 
% 34.13/34.39           (k3_tarski @ (k2_tarski @ X0 @ (k2_relat_1 @ sk_B_1))))
% 34.13/34.39           = (k1_xboole_0))),
% 34.13/34.39      inference('sup+', [status(thm)], ['123', '130'])).
% 34.13/34.39  thf('132', plain,
% 34.13/34.39      (![X56 : $i]:
% 34.13/34.39         (((k3_relat_1 @ X56)
% 34.13/34.39            = (k3_tarski @ 
% 34.13/34.39               (k2_tarski @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 34.13/34.39          | ~ (v1_relat_1 @ X56))),
% 34.13/34.39      inference('demod', [status(thm)], ['1', '2'])).
% 34.13/34.39  thf('133', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 34.13/34.39      inference('simplify', [status(thm)], ['105'])).
% 34.13/34.39  thf('134', plain,
% 34.13/34.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X11 @ X12)
% 34.13/34.39          | (r1_tarski @ X11 @ (k3_tarski @ (k2_tarski @ X13 @ X12))))),
% 34.13/34.39      inference('demod', [status(thm)], ['10', '11'])).
% 34.13/34.39  thf('135', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['133', '134'])).
% 34.13/34.39  thf('136', plain,
% 34.13/34.39      (![X0 : $i]:
% 34.13/34.39         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 34.13/34.39          | ~ (v1_relat_1 @ X0))),
% 34.13/34.39      inference('sup+', [status(thm)], ['132', '135'])).
% 34.13/34.39  thf(t36_xboole_1, axiom,
% 34.13/34.39    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 34.13/34.39  thf('137', plain,
% 34.13/34.39      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 34.13/34.39      inference('cnf', [status(esa)], [t36_xboole_1])).
% 34.13/34.39  thf('138', plain,
% 34.13/34.39      (![X15 : $i, X16 : $i, X17 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X15 @ X16)
% 34.13/34.39          | ~ (r1_tarski @ X16 @ X17)
% 34.13/34.39          | (r1_tarski @ X15 @ X17))),
% 34.13/34.39      inference('cnf', [status(esa)], [t1_xboole_1])).
% 34.13/34.39  thf('139', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.13/34.39         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 34.13/34.39      inference('sup-', [status(thm)], ['137', '138'])).
% 34.13/34.39  thf('140', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (~ (v1_relat_1 @ X0)
% 34.13/34.39          | (r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ X0) @ X1) @ 
% 34.13/34.39             (k3_relat_1 @ X0)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['136', '139'])).
% 34.13/34.39  thf('141', plain,
% 34.13/34.39      (![X0 : $i]:
% 34.13/34.39         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 34.13/34.39          | ~ (v1_relat_1 @ X0))),
% 34.13/34.39      inference('sup+', [status(thm)], ['3', '6'])).
% 34.13/34.39  thf('142', plain,
% 34.13/34.39      (![X32 : $i, X33 : $i, X34 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X32 @ X33)
% 34.13/34.39          | ~ (r1_tarski @ X34 @ X33)
% 34.13/34.39          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X32 @ X34)) @ X33))),
% 34.13/34.39      inference('demod', [status(thm)], ['116', '117'])).
% 34.13/34.39  thf('143', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (~ (v1_relat_1 @ X0)
% 34.13/34.39          | (r1_tarski @ (k3_tarski @ (k2_tarski @ (k1_relat_1 @ X0) @ X1)) @ 
% 34.13/34.39             (k3_relat_1 @ X0))
% 34.13/34.39          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['141', '142'])).
% 34.13/34.39  thf('144', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (~ (v1_relat_1 @ X0)
% 34.13/34.39          | (r1_tarski @ 
% 34.13/34.39             (k3_tarski @ 
% 34.13/34.39              (k2_tarski @ (k1_relat_1 @ X0) @ 
% 34.13/34.39               (k4_xboole_0 @ (k2_relat_1 @ X0) @ X1))) @ 
% 34.13/34.39             (k3_relat_1 @ X0))
% 34.13/34.39          | ~ (v1_relat_1 @ X0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['140', '143'])).
% 34.13/34.39  thf('145', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         ((r1_tarski @ 
% 34.13/34.39           (k3_tarski @ 
% 34.13/34.39            (k2_tarski @ (k1_relat_1 @ X0) @ 
% 34.13/34.39             (k4_xboole_0 @ (k2_relat_1 @ X0) @ X1))) @ 
% 34.13/34.39           (k3_relat_1 @ X0))
% 34.13/34.39          | ~ (v1_relat_1 @ X0))),
% 34.13/34.39      inference('simplify', [status(thm)], ['144'])).
% 34.13/34.39  thf('146', plain,
% 34.13/34.39      (((r1_tarski @ 
% 34.13/34.39         (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ k1_xboole_0)) @ 
% 34.13/34.39         (k3_relat_1 @ sk_A))
% 34.13/34.39        | ~ (v1_relat_1 @ sk_A))),
% 34.13/34.39      inference('sup+', [status(thm)], ['131', '145'])).
% 34.13/34.39  thf('147', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf('148', plain,
% 34.13/34.39      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 34.13/34.39      inference('sup+', [status(thm)], ['29', '32'])).
% 34.13/34.39  thf('149', plain, ((v1_relat_1 @ sk_A)),
% 34.13/34.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.13/34.39  thf('150', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))),
% 34.13/34.39      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 34.13/34.39  thf('151', plain,
% 34.13/34.39      (![X0 : $i, X1 : $i]:
% 34.13/34.39         (~ (r1_tarski @ X1 @ X0)
% 34.13/34.39          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['51', '52'])).
% 34.13/34.39  thf('152', plain,
% 34.13/34.39      ((r1_tarski @ 
% 34.13/34.39        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A)) @ k1_xboole_0)),
% 34.13/34.39      inference('sup-', [status(thm)], ['150', '151'])).
% 34.13/34.39  thf('153', plain,
% 34.13/34.39      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 34.13/34.39      inference('sup-', [status(thm)], ['19', '20'])).
% 34.13/34.39  thf('154', plain,
% 34.13/34.39      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_A))
% 34.13/34.39         = (k1_xboole_0))),
% 34.13/34.39      inference('sup-', [status(thm)], ['152', '153'])).
% 34.13/34.39  thf('155', plain,
% 34.13/34.39      (![X21 : $i, X22 : $i]:
% 34.13/34.39         ((k3_tarski @ (k2_tarski @ X21 @ (k4_xboole_0 @ X22 @ X21)))
% 34.13/34.39           = (k3_tarski @ (k2_tarski @ X21 @ X22)))),
% 34.13/34.39      inference('demod', [status(thm)], ['23', '24', '25'])).
% 34.13/34.39  thf('156', plain,
% 34.13/34.39      (((k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_A) @ k1_xboole_0))
% 34.13/34.39         = (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))))),
% 34.13/34.39      inference('sup+', [status(thm)], ['154', '155'])).
% 34.13/34.39  thf('157', plain,
% 34.13/34.39      (![X35 : $i, X36 : $i]:
% 34.13/34.39         ((k2_tarski @ X36 @ X35) = (k2_tarski @ X35 @ X36))),
% 34.13/34.39      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 34.13/34.39  thf('158', plain,
% 34.13/34.39      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 34.13/34.39      inference('sup+', [status(thm)], ['29', '32'])).
% 34.13/34.39  thf('159', plain,
% 34.13/34.39      (((k3_relat_1 @ sk_A)
% 34.13/34.39         = (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A))))),
% 34.13/34.39      inference('demod', [status(thm)], ['156', '157', '158'])).
% 34.13/34.39  thf('160', plain,
% 34.13/34.39      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 34.13/34.39      inference('demod', [status(thm)], ['120', '121', '122', '159'])).
% 34.13/34.39  thf('161', plain, ($false), inference('demod', [status(thm)], ['0', '160'])).
% 34.13/34.39  
% 34.13/34.39  % SZS output end Refutation
% 34.13/34.39  
% 34.16/34.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
