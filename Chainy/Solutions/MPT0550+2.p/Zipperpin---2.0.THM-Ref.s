%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0550+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ERtT2P15cs

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 11.17s
% Output     : Refutation 11.17s
% Verified   : 
% Statistics : Number of formulae       :   72 (  93 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  400 ( 562 expanded)
%              Number of equality atoms :   46 (  75 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_14_type,type,(
    sk_B_14: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('0',plain,(
    ! [X77: $i] :
      ( ( X77 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
        = B ) ) )).

thf('3',plain,(
    ! [X1026: $i,X1027: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1027 @ X1026 ) )
        = X1026 )
      | ~ ( r2_hidden @ ( X1027 @ X1026 ) ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ ( X0 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X363: $i,X364: $i] :
      ( r1_tarski @ ( X363 @ ( k2_xboole_0 @ ( X363 @ X364 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('9',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t152_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ ( A @ ( k1_relat_1 @ B ) ) )
          & ( ( k9_relat_1 @ ( B @ A ) )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ ( A @ ( k1_relat_1 @ B ) ) )
            & ( ( k9_relat_1 @ ( B @ A ) )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_relat_1])).

thf('10',plain,(
    r1_tarski @ ( sk_A_5 @ ( k1_relat_1 @ sk_B_14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ ( k1_relat_1 @ sk_B_14 ) ) )
      | ~ ( r2_hidden @ ( X0 @ sk_A_5 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A_5 = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_A_5 @ ( k1_relat_1 @ sk_B_14 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_A_5 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    sk_A_5 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_B_1 @ sk_A_5 @ ( k1_relat_1 @ sk_B_14 ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','16'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('18',plain,(
    ! [X1021: $i,X1023: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1021 @ X1023 ) )
      | ~ ( r2_hidden @ ( X1021 @ X1023 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B_1 @ sk_A_5 ) @ ( k1_relat_1 @ sk_B_14 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( A @ C ) )
        & ( r1_xboole_0 @ ( B @ C ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X320: $i,X321: $i,X322: $i] :
      ( ( X320 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X320 @ X321 ) )
      | ~ ( r1_tarski @ ( X320 @ X322 ) )
      | ~ ( r1_xboole_0 @ ( X321 @ X322 ) ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,(
    ! [X320: $i,X321: $i,X322: $i] :
      ( ( X320 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X320 @ X321 ) )
      | ~ ( r1_tarski @ ( X320 @ X322 ) )
      | ~ ( r1_xboole_0 @ ( X321 @ X322 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_14 @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ ( sk_B_1 @ sk_A_5 ) @ X0 ) )
      | ( ( k1_tarski @ ( sk_B_1 @ sk_A_5 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('24',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
     != k1_xboole_0 ) )).

thf('25',plain,(
    ! [X1343: $i,X1344: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1343 @ X1344 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,(
    ! [X1343: $i,X1344: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1343 @ X1344 ) )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_14 @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ ( sk_B_1 @ sk_A_5 ) @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_14 @ ( k2_xboole_0 @ ( k1_tarski @ ( sk_B_1 @ sk_A_5 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_14 @ ( k2_xboole_0 @ ( X0 @ ( k1_tarski @ ( sk_B_1 @ sk_A_5 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','30'])).

thf('32',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_14 @ sk_A_5 ) )
    | ( sk_A_5 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','31'])).

thf('33',plain,(
    sk_A_5 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_14 @ sk_A_5 ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k9_relat_1 @ ( sk_B_14 @ sk_A_5 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('37',plain,
    ( ( k9_relat_1 @ ( sk_B_14 @ sk_A_5 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ ( B @ A ) )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B @ A ) ) ) ) )).

thf('38',plain,(
    ! [X2271: $i,X2272: $i] :
      ( ( ( k9_relat_1 @ ( X2271 @ X2272 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X2271 @ X2272 ) )
      | ~ ( v1_relat_1 @ X2271 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('39',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('40',plain,(
    ! [X2271: $i,X2272: $i] :
      ( ( ( k9_relat_1 @ ( X2271 @ X2272 ) )
       != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X2271 @ X2272 ) )
      | ~ ( v1_relat_1 @ X2271 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_14 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_14 @ sk_A_5 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_14 @ sk_A_5 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_14 @ sk_A_5 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['34','44'])).

%------------------------------------------------------------------------------
