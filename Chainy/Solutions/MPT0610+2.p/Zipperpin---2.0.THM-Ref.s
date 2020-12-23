%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0610+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CrhQaNxpKW

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 12.21s
% Output     : Refutation 12.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  259 ( 375 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(sk_A_6_type,type,(
    sk_A_6: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t214_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k1_relat_1 @ A @ ( k1_relat_1 @ B ) ) )
           => ( r1_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k1_relat_1 @ A @ ( k1_relat_1 @ B ) ) )
             => ( r1_xboole_0 @ ( A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t214_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ ( A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2162: $i,X2163: $i] :
      ( ~ ( v1_relat_1 @ X2162 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ ( X2162 @ X2163 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('2',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A_6 @ ( k1_relat_1 @ sk_B_15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A_6 @ ( k1_relat_1 @ sk_B_15 ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ ( A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X2303: $i,X2304: $i] :
      ( ~ ( v1_relat_1 @ X2303 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ ( X2304 @ X2303 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X2304 @ ( k1_relat_1 @ X2303 ) ) ) ) )
      | ~ ( v1_relat_1 @ X2304 ) ) ),
    inference(cnf,[status(esa)],[t14_relat_1])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) @ o_0_0_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A_6 )
    | ~ ( v1_relat_1 @ sk_B_15 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ ( A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X245: $i] :
      ( ( X245 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X245: $i] :
      ( ( X245 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( k1_relat_1 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['11','15'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X2181: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X2181 ) )
      | ~ ( v1_relat_1 @ X2181 )
      | ( v1_xboole_0 @ X2181 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_A_6 )
    | ( v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A_6 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( sk_A_6 @ sk_B_15 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('30',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    r1_xboole_0 @ ( sk_A_6 @ sk_B_15 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
