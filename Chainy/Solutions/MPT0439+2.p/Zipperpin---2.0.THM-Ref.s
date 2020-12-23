%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0439+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oabs1RsrPE

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 44.72s
% Output     : Refutation 44.72s
% Verified   : 
% Statistics : Number of formulae       :   19 (  21 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :   87 ( 109 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_4_type,type,(
    sk_A_4: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ ( A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X2081: $i] :
      ( ( r1_tarski @ ( X2081 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X2081 @ ( k2_relat_1 @ X2081 ) ) ) ) )
      | ~ ( v1_relat_1 @ X2081 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t22_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ ( A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A @ ( k2_relat_1 @ A ) ) ) ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k3_xboole_0 @ ( A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A @ ( k2_relat_1 @ A ) ) ) ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t22_relat_1])).

thf('3',plain,(
    ( k3_xboole_0 @ ( sk_A_4 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A_4 @ ( k2_relat_1 @ sk_A_4 ) ) ) ) )
 != sk_A_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A_4 != sk_A_4 )
    | ~ ( v1_relat_1 @ sk_A_4 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_A_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_A_4 != sk_A_4 ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
