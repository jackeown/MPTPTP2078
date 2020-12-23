%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0583+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b1BbCsr99T

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 156 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t187_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ ( B @ ( k1_relat_1 @ A ) ) )
         => ( ( k7_relat_1 @ ( A @ B ) )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( r1_xboole_0 @ ( B @ ( k1_relat_1 @ A ) ) )
           => ( ( k7_relat_1 @ ( A @ B ) )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t187_relat_1])).

thf('0',plain,(
    r1_xboole_0 @ ( sk_B_15 @ ( k1_relat_1 @ sk_A_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A_5 @ sk_B_15 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ ( B @ A ) )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X2502: $i,X2503: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X2502 @ X2503 ) )
      | ( ( k7_relat_1 @ ( X2502 @ X2503 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2502 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X2502: $i,X2503: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X2502 @ X2503 ) )
      | ( ( k7_relat_1 @ ( X2502 @ X2503 ) )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X2502 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_A_5 )
    | ( ( k7_relat_1 @ ( sk_A_5 @ sk_B_15 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k7_relat_1 @ ( sk_A_5 @ sk_B_15 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k7_relat_1 @ ( sk_A_5 @ sk_B_15 ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    ( k7_relat_1 @ ( sk_A_5 @ sk_B_15 ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

%------------------------------------------------------------------------------
