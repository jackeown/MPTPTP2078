%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0473+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NiWiGWri9V

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  83 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  248 ( 665 expanded)
%              Number of equality atoms :   61 ( 154 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
        <=> ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_relat_1])).

thf('0',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('5',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('12',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k1_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k2_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_relat_1 @ sk_A )
       != k1_xboole_0 )
      & ( ( k2_relat_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','20','21'])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['8','22'])).

thf('24',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','23','24'])).

thf('26',plain,
    ( $false
   <= ( ( k2_relat_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ( k2_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['9','20'])).

thf('28',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['26','27'])).


%------------------------------------------------------------------------------
