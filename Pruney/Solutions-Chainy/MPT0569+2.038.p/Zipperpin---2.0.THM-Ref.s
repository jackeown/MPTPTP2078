%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2GPwTVnLiL

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:07 EST 2020

% Result     : Theorem 43.27s
% Output     : Refutation 43.27s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 153 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  752 (1591 expanded)
%              Number of equality atoms :   28 (  76 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t173_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t173_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

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

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k10_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( sk_D_1 @ X16 @ X14 @ X15 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k10_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( sk_D_1 @ X16 @ X14 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k10_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','27'])).

thf('29',plain,(
    ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,
    ( ( k10_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','27','31'])).

thf('33',plain,
    ( ( k10_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X13 ) @ X16 )
      | ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ X15 @ ( k10_relat_1 @ X16 @ X14 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_relat_1 @ X1 ) @ ( sk_C @ X0 @ ( k2_relat_1 @ X1 ) ) ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_relat_1 @ X1 ) @ ( sk_C @ X0 @ ( k2_relat_1 @ X1 ) ) ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['33','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('52',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['51','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['29','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2GPwTVnLiL
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:13:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 43.27/43.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 43.27/43.53  % Solved by: fo/fo7.sh
% 43.27/43.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 43.27/43.53  % done 40442 iterations in 43.067s
% 43.27/43.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 43.27/43.53  % SZS output start Refutation
% 43.27/43.53  thf(sk_A_type, type, sk_A: $i).
% 43.27/43.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 43.27/43.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 43.27/43.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 43.27/43.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 43.27/43.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 43.27/43.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 43.27/43.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 43.27/43.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 43.27/43.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 43.27/43.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 43.27/43.53  thf(sk_B_type, type, sk_B: $i > $i).
% 43.27/43.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 43.27/43.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 43.27/43.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 43.27/43.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 43.27/43.53  thf(t173_relat_1, conjecture,
% 43.27/43.53    (![A:$i,B:$i]:
% 43.27/43.53     ( ( v1_relat_1 @ B ) =>
% 43.27/43.53       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 43.27/43.53         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 43.27/43.53  thf(zf_stmt_0, negated_conjecture,
% 43.27/43.53    (~( ![A:$i,B:$i]:
% 43.27/43.53        ( ( v1_relat_1 @ B ) =>
% 43.27/43.53          ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 43.27/43.53            ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )),
% 43.27/43.53    inference('cnf.neg', [status(esa)], [t173_relat_1])).
% 43.27/43.53  thf('0', plain,
% 43.27/43.53      ((~ (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)
% 43.27/43.53        | ((k10_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 43.27/43.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.27/43.53  thf('1', plain,
% 43.27/43.53      ((~ (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))
% 43.27/43.53         <= (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 43.27/43.53      inference('split', [status(esa)], ['0'])).
% 43.27/43.53  thf('2', plain,
% 43.27/43.53      (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)) | 
% 43.27/43.53       ~ (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 43.27/43.53      inference('split', [status(esa)], ['0'])).
% 43.27/43.53  thf('3', plain,
% 43.27/43.53      (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)
% 43.27/43.53        | ((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 43.27/43.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.27/43.53  thf('4', plain,
% 43.27/43.53      (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))
% 43.27/43.53         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 43.27/43.53      inference('split', [status(esa)], ['3'])).
% 43.27/43.53  thf(t3_xboole_0, axiom,
% 43.27/43.53    (![A:$i,B:$i]:
% 43.27/43.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 43.27/43.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 43.27/43.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 43.27/43.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 43.27/43.53  thf('5', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 43.27/43.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 43.27/43.53  thf('6', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 43.27/43.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 43.27/43.53  thf('7', plain,
% 43.27/43.53      (![X0 : $i, X2 : $i, X3 : $i]:
% 43.27/43.53         (~ (r2_hidden @ X2 @ X0)
% 43.27/43.53          | ~ (r2_hidden @ X2 @ X3)
% 43.27/43.53          | ~ (r1_xboole_0 @ X0 @ X3))),
% 43.27/43.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 43.27/43.53  thf('8', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.27/43.53         ((r1_xboole_0 @ X1 @ X0)
% 43.27/43.53          | ~ (r1_xboole_0 @ X0 @ X2)
% 43.27/43.53          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 43.27/43.53      inference('sup-', [status(thm)], ['6', '7'])).
% 43.27/43.53  thf('9', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         ((r1_xboole_0 @ X0 @ X1)
% 43.27/43.53          | ~ (r1_xboole_0 @ X1 @ X0)
% 43.27/43.53          | (r1_xboole_0 @ X0 @ X1))),
% 43.27/43.53      inference('sup-', [status(thm)], ['5', '8'])).
% 43.27/43.53  thf('10', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 43.27/43.53      inference('simplify', [status(thm)], ['9'])).
% 43.27/43.53  thf('11', plain,
% 43.27/43.53      (((r1_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1)))
% 43.27/43.53         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 43.27/43.53      inference('sup-', [status(thm)], ['4', '10'])).
% 43.27/43.53  thf(t7_xboole_0, axiom,
% 43.27/43.53    (![A:$i]:
% 43.27/43.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 43.27/43.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 43.27/43.53  thf('12', plain,
% 43.27/43.53      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 43.27/43.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 43.27/43.53  thf(t166_relat_1, axiom,
% 43.27/43.53    (![A:$i,B:$i,C:$i]:
% 43.27/43.53     ( ( v1_relat_1 @ C ) =>
% 43.27/43.53       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 43.27/43.53         ( ?[D:$i]:
% 43.27/43.53           ( ( r2_hidden @ D @ B ) & 
% 43.27/43.53             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 43.27/43.53             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 43.27/43.53  thf('13', plain,
% 43.27/43.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 43.27/43.53         (~ (r2_hidden @ X15 @ (k10_relat_1 @ X16 @ X14))
% 43.27/43.53          | (r2_hidden @ (sk_D_1 @ X16 @ X14 @ X15) @ (k2_relat_1 @ X16))
% 43.27/43.53          | ~ (v1_relat_1 @ X16))),
% 43.27/43.53      inference('cnf', [status(esa)], [t166_relat_1])).
% 43.27/43.53  thf('14', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 43.27/43.53          | ~ (v1_relat_1 @ X1)
% 43.27/43.53          | (r2_hidden @ 
% 43.27/43.53             (sk_D_1 @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0))) @ 
% 43.27/43.53             (k2_relat_1 @ X1)))),
% 43.27/43.53      inference('sup-', [status(thm)], ['12', '13'])).
% 43.27/43.53  thf('15', plain,
% 43.27/43.53      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 43.27/43.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 43.27/43.53  thf('16', plain,
% 43.27/43.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 43.27/43.53         (~ (r2_hidden @ X15 @ (k10_relat_1 @ X16 @ X14))
% 43.27/43.53          | (r2_hidden @ (sk_D_1 @ X16 @ X14 @ X15) @ X14)
% 43.27/43.53          | ~ (v1_relat_1 @ X16))),
% 43.27/43.53      inference('cnf', [status(esa)], [t166_relat_1])).
% 43.27/43.53  thf('17', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 43.27/43.53          | ~ (v1_relat_1 @ X1)
% 43.27/43.53          | (r2_hidden @ 
% 43.27/43.53             (sk_D_1 @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0))) @ X0))),
% 43.27/43.53      inference('sup-', [status(thm)], ['15', '16'])).
% 43.27/43.53  thf('18', plain,
% 43.27/43.53      (![X0 : $i, X2 : $i, X3 : $i]:
% 43.27/43.53         (~ (r2_hidden @ X2 @ X0)
% 43.27/43.53          | ~ (r2_hidden @ X2 @ X3)
% 43.27/43.53          | ~ (r1_xboole_0 @ X0 @ X3))),
% 43.27/43.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 43.27/43.53  thf('19', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.27/43.53         (~ (v1_relat_1 @ X1)
% 43.27/43.53          | ((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 43.27/43.53          | ~ (r1_xboole_0 @ X0 @ X2)
% 43.27/43.53          | ~ (r2_hidden @ 
% 43.27/43.53               (sk_D_1 @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0))) @ X2))),
% 43.27/43.53      inference('sup-', [status(thm)], ['17', '18'])).
% 43.27/43.53  thf('20', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         (~ (v1_relat_1 @ X0)
% 43.27/43.53          | ((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 43.27/43.53          | ~ (r1_xboole_0 @ X1 @ (k2_relat_1 @ X0))
% 43.27/43.53          | ((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 43.27/43.53          | ~ (v1_relat_1 @ X0))),
% 43.27/43.53      inference('sup-', [status(thm)], ['14', '19'])).
% 43.27/43.53  thf('21', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         (~ (r1_xboole_0 @ X1 @ (k2_relat_1 @ X0))
% 43.27/43.53          | ((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 43.27/43.53          | ~ (v1_relat_1 @ X0))),
% 43.27/43.53      inference('simplify', [status(thm)], ['20'])).
% 43.27/43.53  thf('22', plain,
% 43.27/43.53      (((~ (v1_relat_1 @ sk_B_1)
% 43.27/43.53         | ((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))
% 43.27/43.53         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 43.27/43.53      inference('sup-', [status(thm)], ['11', '21'])).
% 43.27/43.53  thf('23', plain, ((v1_relat_1 @ sk_B_1)),
% 43.27/43.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.27/43.53  thf('24', plain,
% 43.27/43.53      ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 43.27/43.53         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 43.27/43.53      inference('demod', [status(thm)], ['22', '23'])).
% 43.27/43.53  thf('25', plain,
% 43.27/43.53      ((((k10_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 43.27/43.53         <= (~ (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 43.27/43.53      inference('split', [status(esa)], ['0'])).
% 43.27/43.53  thf('26', plain,
% 43.27/43.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 43.27/43.53         <= (~ (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 43.27/43.53             ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 43.27/43.53      inference('sup-', [status(thm)], ['24', '25'])).
% 43.27/43.53  thf('27', plain,
% 43.27/43.53      ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 43.27/43.53       ~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 43.27/43.53      inference('simplify', [status(thm)], ['26'])).
% 43.27/43.53  thf('28', plain, (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 43.27/43.53      inference('sat_resolution*', [status(thm)], ['2', '27'])).
% 43.27/43.53  thf('29', plain, (~ (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 43.27/43.53      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 43.27/43.53  thf('30', plain,
% 43.27/43.53      ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 43.27/43.53         <= ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 43.27/43.53      inference('split', [status(esa)], ['3'])).
% 43.27/43.53  thf('31', plain,
% 43.27/43.53      ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 43.27/43.53       ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 43.27/43.53      inference('split', [status(esa)], ['3'])).
% 43.27/43.53  thf('32', plain, ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 43.27/43.53      inference('sat_resolution*', [status(thm)], ['2', '27', '31'])).
% 43.27/43.53  thf('33', plain, (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 43.27/43.53      inference('simpl_trail', [status(thm)], ['30', '32'])).
% 43.27/43.53  thf('34', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 43.27/43.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 43.27/43.53  thf('35', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 43.27/43.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 43.27/43.53  thf('36', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 43.27/43.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 43.27/43.53  thf(t146_relat_1, axiom,
% 43.27/43.53    (![A:$i]:
% 43.27/43.53     ( ( v1_relat_1 @ A ) =>
% 43.27/43.53       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 43.27/43.53  thf('37', plain,
% 43.27/43.53      (![X12 : $i]:
% 43.27/43.53         (((k9_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (k2_relat_1 @ X12))
% 43.27/43.53          | ~ (v1_relat_1 @ X12))),
% 43.27/43.53      inference('cnf', [status(esa)], [t146_relat_1])).
% 43.27/43.53  thf(t143_relat_1, axiom,
% 43.27/43.53    (![A:$i,B:$i,C:$i]:
% 43.27/43.53     ( ( v1_relat_1 @ C ) =>
% 43.27/43.53       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 43.27/43.53         ( ?[D:$i]:
% 43.27/43.53           ( ( r2_hidden @ D @ B ) & 
% 43.27/43.53             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 43.27/43.53             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 43.27/43.53  thf('38', plain,
% 43.27/43.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 43.27/43.53         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 43.27/43.53          | (r2_hidden @ (k4_tarski @ (sk_D @ X11 @ X9 @ X10) @ X10) @ X11)
% 43.27/43.53          | ~ (v1_relat_1 @ X11))),
% 43.27/43.53      inference('cnf', [status(esa)], [t143_relat_1])).
% 43.27/43.53  thf('39', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 43.27/43.53          | ~ (v1_relat_1 @ X0)
% 43.27/43.53          | ~ (v1_relat_1 @ X0)
% 43.27/43.53          | (r2_hidden @ 
% 43.27/43.53             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 43.27/43.53      inference('sup-', [status(thm)], ['37', '38'])).
% 43.27/43.53  thf('40', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         ((r2_hidden @ 
% 43.27/43.53           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 43.27/43.53          | ~ (v1_relat_1 @ X0)
% 43.27/43.53          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 43.27/43.53      inference('simplify', [status(thm)], ['39'])).
% 43.27/43.53  thf('41', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         ((r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 43.27/43.53          | ~ (v1_relat_1 @ X0)
% 43.27/43.53          | (r2_hidden @ 
% 43.27/43.53             (k4_tarski @ 
% 43.27/43.53              (sk_D @ X0 @ (k1_relat_1 @ X0) @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 43.27/43.53              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 43.27/43.53             X0))),
% 43.27/43.53      inference('sup-', [status(thm)], ['36', '40'])).
% 43.27/43.53  thf('42', plain,
% 43.27/43.53      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 43.27/43.53         (~ (r2_hidden @ X13 @ X14)
% 43.27/43.53          | ~ (r2_hidden @ (k4_tarski @ X15 @ X13) @ X16)
% 43.27/43.53          | ~ (r2_hidden @ X13 @ (k2_relat_1 @ X16))
% 43.27/43.53          | (r2_hidden @ X15 @ (k10_relat_1 @ X16 @ X14))
% 43.27/43.53          | ~ (v1_relat_1 @ X16))),
% 43.27/43.53      inference('cnf', [status(esa)], [t166_relat_1])).
% 43.27/43.53  thf('43', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.27/43.53         (~ (v1_relat_1 @ X0)
% 43.27/43.53          | (r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 43.27/43.53          | ~ (v1_relat_1 @ X0)
% 43.27/43.53          | (r2_hidden @ 
% 43.27/43.53             (sk_D @ X0 @ (k1_relat_1 @ X0) @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 43.27/43.53             (k10_relat_1 @ X0 @ X2))
% 43.27/43.53          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ (k2_relat_1 @ X0))
% 43.27/43.53          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2))),
% 43.27/43.53      inference('sup-', [status(thm)], ['41', '42'])).
% 43.27/43.53  thf('44', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.27/43.53         (~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2)
% 43.27/43.53          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ (k2_relat_1 @ X0))
% 43.27/43.53          | (r2_hidden @ 
% 43.27/43.53             (sk_D @ X0 @ (k1_relat_1 @ X0) @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 43.27/43.53             (k10_relat_1 @ X0 @ X2))
% 43.27/43.53          | (r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 43.27/43.53          | ~ (v1_relat_1 @ X0))),
% 43.27/43.53      inference('simplify', [status(thm)], ['43'])).
% 43.27/43.53  thf('45', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.27/43.53         ((r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 43.27/43.53          | ~ (v1_relat_1 @ X0)
% 43.27/43.53          | (r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 43.27/43.53          | (r2_hidden @ 
% 43.27/43.53             (sk_D @ X0 @ (k1_relat_1 @ X0) @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 43.27/43.53             (k10_relat_1 @ X0 @ X2))
% 43.27/43.53          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2))),
% 43.27/43.53      inference('sup-', [status(thm)], ['35', '44'])).
% 43.27/43.53  thf('46', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.27/43.53         (~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2)
% 43.27/43.53          | (r2_hidden @ 
% 43.27/43.53             (sk_D @ X0 @ (k1_relat_1 @ X0) @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 43.27/43.53             (k10_relat_1 @ X0 @ X2))
% 43.27/43.53          | ~ (v1_relat_1 @ X0)
% 43.27/43.53          | (r1_xboole_0 @ (k2_relat_1 @ X0) @ X1))),
% 43.27/43.53      inference('simplify', [status(thm)], ['45'])).
% 43.27/43.53  thf('47', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         ((r1_xboole_0 @ (k2_relat_1 @ X1) @ X0)
% 43.27/43.53          | (r1_xboole_0 @ (k2_relat_1 @ X1) @ X0)
% 43.27/43.53          | ~ (v1_relat_1 @ X1)
% 43.27/43.53          | (r2_hidden @ 
% 43.27/43.53             (sk_D @ X1 @ (k1_relat_1 @ X1) @ (sk_C @ X0 @ (k2_relat_1 @ X1))) @ 
% 43.27/43.53             (k10_relat_1 @ X1 @ X0)))),
% 43.27/43.53      inference('sup-', [status(thm)], ['34', '46'])).
% 43.27/43.53  thf('48', plain,
% 43.27/43.53      (![X0 : $i, X1 : $i]:
% 43.27/43.53         ((r2_hidden @ 
% 43.27/43.53           (sk_D @ X1 @ (k1_relat_1 @ X1) @ (sk_C @ X0 @ (k2_relat_1 @ X1))) @ 
% 43.27/43.53           (k10_relat_1 @ X1 @ X0))
% 43.27/43.53          | ~ (v1_relat_1 @ X1)
% 43.27/43.53          | (r1_xboole_0 @ (k2_relat_1 @ X1) @ X0))),
% 43.27/43.53      inference('simplify', [status(thm)], ['47'])).
% 43.27/43.53  thf('49', plain,
% 43.27/43.53      (((r2_hidden @ 
% 43.27/43.53         (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ 
% 43.27/43.53          (sk_C @ sk_A @ (k2_relat_1 @ sk_B_1))) @ 
% 43.27/43.53         k1_xboole_0)
% 43.27/43.53        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)
% 43.27/43.53        | ~ (v1_relat_1 @ sk_B_1))),
% 43.27/43.53      inference('sup+', [status(thm)], ['33', '48'])).
% 43.27/43.53  thf('50', plain, ((v1_relat_1 @ sk_B_1)),
% 43.27/43.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.27/43.53  thf('51', plain,
% 43.27/43.53      (((r2_hidden @ 
% 43.27/43.53         (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ 
% 43.27/43.53          (sk_C @ sk_A @ (k2_relat_1 @ sk_B_1))) @ 
% 43.27/43.53         k1_xboole_0)
% 43.27/43.53        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 43.27/43.53      inference('demod', [status(thm)], ['49', '50'])).
% 43.27/43.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 43.27/43.53  thf('52', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 43.27/43.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 43.27/43.53  thf(l24_zfmisc_1, axiom,
% 43.27/43.53    (![A:$i,B:$i]:
% 43.27/43.53     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 43.27/43.53  thf('53', plain,
% 43.27/43.53      (![X6 : $i, X7 : $i]:
% 43.27/43.53         (~ (r1_xboole_0 @ (k1_tarski @ X6) @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 43.27/43.53      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 43.27/43.53  thf('54', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 43.27/43.53      inference('sup-', [status(thm)], ['52', '53'])).
% 43.27/43.53  thf('55', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 43.27/43.53      inference('clc', [status(thm)], ['51', '54'])).
% 43.27/43.53  thf('56', plain, ($false), inference('demod', [status(thm)], ['29', '55'])).
% 43.27/43.53  
% 43.27/43.53  % SZS output end Refutation
% 43.27/43.53  
% 43.27/43.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
