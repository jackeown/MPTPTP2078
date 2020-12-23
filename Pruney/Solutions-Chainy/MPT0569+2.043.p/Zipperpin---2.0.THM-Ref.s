%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hQgdNoD9uP

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:07 EST 2020

% Result     : Theorem 42.54s
% Output     : Refutation 42.54s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 173 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  816 (1825 expanded)
%              Number of equality atoms :   25 (  70 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k10_relat_1 @ X31 @ X29 ) )
      | ( r2_hidden @ ( sk_D_1 @ X31 @ X29 @ X30 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k10_relat_1 @ X31 @ X29 ) )
      | ( r2_hidden @ ( sk_D_1 @ X31 @ X29 @ X30 ) @ X29 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B_1 )
        | ( r1_xboole_0 @ ( k10_relat_1 @ sk_B_1 @ sk_A ) @ X0 ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k10_relat_1 @ sk_B_1 @ sk_A ) @ X0 )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('26',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','34'])).

thf('36',plain,(
    ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('37',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,
    ( ( k10_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','34','38'])).

thf('40',plain,
    ( ( k10_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X27: $i] :
      ( ( ( k9_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k9_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X26 @ X24 @ X25 ) @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ X28 ) @ X31 )
      | ~ ( r2_hidden @ X28 @ ( k2_relat_1 @ X31 ) )
      | ( r2_hidden @ X30 @ ( k10_relat_1 @ X31 @ X29 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k1_relat_1 @ X1 ) @ ( sk_C @ X0 @ ( k2_relat_1 @ X1 ) ) ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_relat_1 @ X1 ) @ ( sk_C @ X0 @ ( k2_relat_1 @ X1 ) ) ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['40','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('59',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('60',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('61',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['58','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['36','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hQgdNoD9uP
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:21:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 42.54/42.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 42.54/42.76  % Solved by: fo/fo7.sh
% 42.54/42.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 42.54/42.76  % done 39910 iterations in 42.308s
% 42.54/42.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 42.54/42.76  % SZS output start Refutation
% 42.54/42.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 42.54/42.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 42.54/42.76  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 42.54/42.76  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 42.54/42.76  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 42.54/42.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 42.54/42.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 42.54/42.76  thf(sk_A_type, type, sk_A: $i).
% 42.54/42.76  thf(sk_B_type, type, sk_B: $i > $i).
% 42.54/42.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 42.54/42.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 42.54/42.76  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 42.54/42.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 42.54/42.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 42.54/42.76  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 42.54/42.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 42.54/42.76  thf(t173_relat_1, conjecture,
% 42.54/42.76    (![A:$i,B:$i]:
% 42.54/42.76     ( ( v1_relat_1 @ B ) =>
% 42.54/42.76       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 42.54/42.76         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 42.54/42.76  thf(zf_stmt_0, negated_conjecture,
% 42.54/42.76    (~( ![A:$i,B:$i]:
% 42.54/42.76        ( ( v1_relat_1 @ B ) =>
% 42.54/42.76          ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 42.54/42.76            ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )),
% 42.54/42.76    inference('cnf.neg', [status(esa)], [t173_relat_1])).
% 42.54/42.76  thf('0', plain,
% 42.54/42.76      ((~ (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)
% 42.54/42.76        | ((k10_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 42.54/42.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.54/42.76  thf('1', plain,
% 42.54/42.76      ((~ (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))
% 42.54/42.76         <= (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 42.54/42.76      inference('split', [status(esa)], ['0'])).
% 42.54/42.76  thf('2', plain,
% 42.54/42.76      (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)) | 
% 42.54/42.76       ~ (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 42.54/42.76      inference('split', [status(esa)], ['0'])).
% 42.54/42.76  thf('3', plain,
% 42.54/42.76      (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)
% 42.54/42.76        | ((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 42.54/42.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.54/42.76  thf('4', plain,
% 42.54/42.76      (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))
% 42.54/42.76         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 42.54/42.76      inference('split', [status(esa)], ['3'])).
% 42.54/42.76  thf(t3_xboole_0, axiom,
% 42.54/42.76    (![A:$i,B:$i]:
% 42.54/42.76     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 42.54/42.76            ( r1_xboole_0 @ A @ B ) ) ) & 
% 42.54/42.76       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 42.54/42.76            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 42.54/42.76  thf('5', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 42.54/42.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.54/42.76  thf('6', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 42.54/42.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.54/42.76  thf('7', plain,
% 42.54/42.76      (![X0 : $i, X2 : $i, X3 : $i]:
% 42.54/42.76         (~ (r2_hidden @ X2 @ X0)
% 42.54/42.76          | ~ (r2_hidden @ X2 @ X3)
% 42.54/42.76          | ~ (r1_xboole_0 @ X0 @ X3))),
% 42.54/42.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.54/42.76  thf('8', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ X1 @ X0)
% 42.54/42.76          | ~ (r1_xboole_0 @ X0 @ X2)
% 42.54/42.76          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 42.54/42.76      inference('sup-', [status(thm)], ['6', '7'])).
% 42.54/42.76  thf('9', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ X0 @ X1)
% 42.54/42.76          | ~ (r1_xboole_0 @ X1 @ X0)
% 42.54/42.76          | (r1_xboole_0 @ X0 @ X1))),
% 42.54/42.76      inference('sup-', [status(thm)], ['5', '8'])).
% 42.54/42.76  thf('10', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 42.54/42.76      inference('simplify', [status(thm)], ['9'])).
% 42.54/42.76  thf('11', plain,
% 42.54/42.76      (((r1_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1)))
% 42.54/42.76         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 42.54/42.76      inference('sup-', [status(thm)], ['4', '10'])).
% 42.54/42.76  thf('12', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 42.54/42.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.54/42.76  thf(t166_relat_1, axiom,
% 42.54/42.76    (![A:$i,B:$i,C:$i]:
% 42.54/42.76     ( ( v1_relat_1 @ C ) =>
% 42.54/42.76       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 42.54/42.76         ( ?[D:$i]:
% 42.54/42.76           ( ( r2_hidden @ D @ B ) & 
% 42.54/42.76             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 42.54/42.76             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 42.54/42.76  thf('13', plain,
% 42.54/42.76      (![X29 : $i, X30 : $i, X31 : $i]:
% 42.54/42.76         (~ (r2_hidden @ X30 @ (k10_relat_1 @ X31 @ X29))
% 42.54/42.76          | (r2_hidden @ (sk_D_1 @ X31 @ X29 @ X30) @ (k2_relat_1 @ X31))
% 42.54/42.76          | ~ (v1_relat_1 @ X31))),
% 42.54/42.76      inference('cnf', [status(esa)], [t166_relat_1])).
% 42.54/42.76  thf('14', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 42.54/42.76          | ~ (v1_relat_1 @ X1)
% 42.54/42.76          | (r2_hidden @ 
% 42.54/42.76             (sk_D_1 @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 42.54/42.76             (k2_relat_1 @ X1)))),
% 42.54/42.76      inference('sup-', [status(thm)], ['12', '13'])).
% 42.54/42.76  thf('15', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 42.54/42.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.54/42.76  thf('16', plain,
% 42.54/42.76      (![X29 : $i, X30 : $i, X31 : $i]:
% 42.54/42.76         (~ (r2_hidden @ X30 @ (k10_relat_1 @ X31 @ X29))
% 42.54/42.76          | (r2_hidden @ (sk_D_1 @ X31 @ X29 @ X30) @ X29)
% 42.54/42.76          | ~ (v1_relat_1 @ X31))),
% 42.54/42.76      inference('cnf', [status(esa)], [t166_relat_1])).
% 42.54/42.76  thf('17', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 42.54/42.76          | ~ (v1_relat_1 @ X1)
% 42.54/42.76          | (r2_hidden @ 
% 42.54/42.76             (sk_D_1 @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ X0))),
% 42.54/42.76      inference('sup-', [status(thm)], ['15', '16'])).
% 42.54/42.76  thf('18', plain,
% 42.54/42.76      (![X0 : $i, X2 : $i, X3 : $i]:
% 42.54/42.76         (~ (r2_hidden @ X2 @ X0)
% 42.54/42.76          | ~ (r2_hidden @ X2 @ X3)
% 42.54/42.76          | ~ (r1_xboole_0 @ X0 @ X3))),
% 42.54/42.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.54/42.76  thf('19', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 42.54/42.76         (~ (v1_relat_1 @ X1)
% 42.54/42.76          | (r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 42.54/42.76          | ~ (r1_xboole_0 @ X0 @ X3)
% 42.54/42.76          | ~ (r2_hidden @ 
% 42.54/42.76               (sk_D_1 @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ X3))),
% 42.54/42.76      inference('sup-', [status(thm)], ['17', '18'])).
% 42.54/42.76  thf('20', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.54/42.76         (~ (v1_relat_1 @ X0)
% 42.54/42.76          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2)
% 42.54/42.76          | ~ (r1_xboole_0 @ X1 @ (k2_relat_1 @ X0))
% 42.54/42.76          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2)
% 42.54/42.76          | ~ (v1_relat_1 @ X0))),
% 42.54/42.76      inference('sup-', [status(thm)], ['14', '19'])).
% 42.54/42.76  thf('21', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.54/42.76         (~ (r1_xboole_0 @ X1 @ (k2_relat_1 @ X0))
% 42.54/42.76          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2)
% 42.54/42.76          | ~ (v1_relat_1 @ X0))),
% 42.54/42.76      inference('simplify', [status(thm)], ['20'])).
% 42.54/42.76  thf('22', plain,
% 42.54/42.76      ((![X0 : $i]:
% 42.54/42.76          (~ (v1_relat_1 @ sk_B_1)
% 42.54/42.76           | (r1_xboole_0 @ (k10_relat_1 @ sk_B_1 @ sk_A) @ X0)))
% 42.54/42.76         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 42.54/42.76      inference('sup-', [status(thm)], ['11', '21'])).
% 42.54/42.76  thf('23', plain, ((v1_relat_1 @ sk_B_1)),
% 42.54/42.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.54/42.76  thf('24', plain,
% 42.54/42.76      ((![X0 : $i]: (r1_xboole_0 @ (k10_relat_1 @ sk_B_1 @ sk_A) @ X0))
% 42.54/42.76         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 42.54/42.76      inference('demod', [status(thm)], ['22', '23'])).
% 42.54/42.76  thf(t7_xboole_0, axiom,
% 42.54/42.76    (![A:$i]:
% 42.54/42.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 42.54/42.76          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 42.54/42.76  thf('25', plain,
% 42.54/42.76      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 42.54/42.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 42.54/42.76  thf('26', plain,
% 42.54/42.76      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 42.54/42.76      inference('cnf', [status(esa)], [t7_xboole_0])).
% 42.54/42.76  thf('27', plain,
% 42.54/42.76      (![X0 : $i, X2 : $i, X3 : $i]:
% 42.54/42.76         (~ (r2_hidden @ X2 @ X0)
% 42.54/42.76          | ~ (r2_hidden @ X2 @ X3)
% 42.54/42.76          | ~ (r1_xboole_0 @ X0 @ X3))),
% 42.54/42.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.54/42.76  thf('28', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         (((X0) = (k1_xboole_0))
% 42.54/42.76          | ~ (r1_xboole_0 @ X0 @ X1)
% 42.54/42.76          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 42.54/42.76      inference('sup-', [status(thm)], ['26', '27'])).
% 42.54/42.76  thf('29', plain,
% 42.54/42.76      (![X0 : $i]:
% 42.54/42.76         (((X0) = (k1_xboole_0))
% 42.54/42.76          | ~ (r1_xboole_0 @ X0 @ X0)
% 42.54/42.76          | ((X0) = (k1_xboole_0)))),
% 42.54/42.76      inference('sup-', [status(thm)], ['25', '28'])).
% 42.54/42.76  thf('30', plain,
% 42.54/42.76      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 42.54/42.76      inference('simplify', [status(thm)], ['29'])).
% 42.54/42.76  thf('31', plain,
% 42.54/42.76      ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 42.54/42.76         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 42.54/42.76      inference('sup-', [status(thm)], ['24', '30'])).
% 42.54/42.76  thf('32', plain,
% 42.54/42.76      ((((k10_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 42.54/42.76         <= (~ (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 42.54/42.76      inference('split', [status(esa)], ['0'])).
% 42.54/42.76  thf('33', plain,
% 42.54/42.76      ((((k1_xboole_0) != (k1_xboole_0)))
% 42.54/42.76         <= (~ (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 42.54/42.76             ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 42.54/42.76      inference('sup-', [status(thm)], ['31', '32'])).
% 42.54/42.76  thf('34', plain,
% 42.54/42.76      ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 42.54/42.76       ~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 42.54/42.76      inference('simplify', [status(thm)], ['33'])).
% 42.54/42.76  thf('35', plain, (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 42.54/42.76      inference('sat_resolution*', [status(thm)], ['2', '34'])).
% 42.54/42.76  thf('36', plain, (~ (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 42.54/42.76      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 42.54/42.76  thf('37', plain,
% 42.54/42.76      ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 42.54/42.76         <= ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 42.54/42.76      inference('split', [status(esa)], ['3'])).
% 42.54/42.76  thf('38', plain,
% 42.54/42.76      ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 42.54/42.76       ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 42.54/42.76      inference('split', [status(esa)], ['3'])).
% 42.54/42.76  thf('39', plain, ((((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 42.54/42.76      inference('sat_resolution*', [status(thm)], ['2', '34', '38'])).
% 42.54/42.76  thf('40', plain, (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 42.54/42.76      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 42.54/42.76  thf('41', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 42.54/42.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.54/42.76  thf('42', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 42.54/42.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.54/42.76  thf('43', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 42.54/42.76      inference('cnf', [status(esa)], [t3_xboole_0])).
% 42.54/42.76  thf(t146_relat_1, axiom,
% 42.54/42.76    (![A:$i]:
% 42.54/42.76     ( ( v1_relat_1 @ A ) =>
% 42.54/42.76       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 42.54/42.76  thf('44', plain,
% 42.54/42.76      (![X27 : $i]:
% 42.54/42.76         (((k9_relat_1 @ X27 @ (k1_relat_1 @ X27)) = (k2_relat_1 @ X27))
% 42.54/42.76          | ~ (v1_relat_1 @ X27))),
% 42.54/42.76      inference('cnf', [status(esa)], [t146_relat_1])).
% 42.54/42.76  thf(t143_relat_1, axiom,
% 42.54/42.76    (![A:$i,B:$i,C:$i]:
% 42.54/42.76     ( ( v1_relat_1 @ C ) =>
% 42.54/42.76       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 42.54/42.76         ( ?[D:$i]:
% 42.54/42.76           ( ( r2_hidden @ D @ B ) & 
% 42.54/42.76             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 42.54/42.76             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 42.54/42.76  thf('45', plain,
% 42.54/42.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 42.54/42.76         (~ (r2_hidden @ X25 @ (k9_relat_1 @ X26 @ X24))
% 42.54/42.76          | (r2_hidden @ (k4_tarski @ (sk_D @ X26 @ X24 @ X25) @ X25) @ X26)
% 42.54/42.76          | ~ (v1_relat_1 @ X26))),
% 42.54/42.76      inference('cnf', [status(esa)], [t143_relat_1])).
% 42.54/42.76  thf('46', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 42.54/42.76          | ~ (v1_relat_1 @ X0)
% 42.54/42.76          | ~ (v1_relat_1 @ X0)
% 42.54/42.76          | (r2_hidden @ 
% 42.54/42.76             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 42.54/42.76      inference('sup-', [status(thm)], ['44', '45'])).
% 42.54/42.76  thf('47', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r2_hidden @ 
% 42.54/42.76           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 42.54/42.76          | ~ (v1_relat_1 @ X0)
% 42.54/42.76          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 42.54/42.76      inference('simplify', [status(thm)], ['46'])).
% 42.54/42.76  thf('48', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 42.54/42.76          | ~ (v1_relat_1 @ X0)
% 42.54/42.76          | (r2_hidden @ 
% 42.54/42.76             (k4_tarski @ 
% 42.54/42.76              (sk_D @ X0 @ (k1_relat_1 @ X0) @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 42.54/42.76              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 42.54/42.76             X0))),
% 42.54/42.76      inference('sup-', [status(thm)], ['43', '47'])).
% 42.54/42.76  thf('49', plain,
% 42.54/42.76      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 42.54/42.76         (~ (r2_hidden @ X28 @ X29)
% 42.54/42.76          | ~ (r2_hidden @ (k4_tarski @ X30 @ X28) @ X31)
% 42.54/42.76          | ~ (r2_hidden @ X28 @ (k2_relat_1 @ X31))
% 42.54/42.76          | (r2_hidden @ X30 @ (k10_relat_1 @ X31 @ X29))
% 42.54/42.76          | ~ (v1_relat_1 @ X31))),
% 42.54/42.76      inference('cnf', [status(esa)], [t166_relat_1])).
% 42.54/42.76  thf('50', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.54/42.76         (~ (v1_relat_1 @ X0)
% 42.54/42.76          | (r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 42.54/42.76          | ~ (v1_relat_1 @ X0)
% 42.54/42.76          | (r2_hidden @ 
% 42.54/42.76             (sk_D @ X0 @ (k1_relat_1 @ X0) @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 42.54/42.76             (k10_relat_1 @ X0 @ X2))
% 42.54/42.76          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ (k2_relat_1 @ X0))
% 42.54/42.76          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2))),
% 42.54/42.76      inference('sup-', [status(thm)], ['48', '49'])).
% 42.54/42.76  thf('51', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.54/42.76         (~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2)
% 42.54/42.76          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ (k2_relat_1 @ X0))
% 42.54/42.76          | (r2_hidden @ 
% 42.54/42.76             (sk_D @ X0 @ (k1_relat_1 @ X0) @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 42.54/42.76             (k10_relat_1 @ X0 @ X2))
% 42.54/42.76          | (r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 42.54/42.76          | ~ (v1_relat_1 @ X0))),
% 42.54/42.76      inference('simplify', [status(thm)], ['50'])).
% 42.54/42.76  thf('52', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 42.54/42.76          | ~ (v1_relat_1 @ X0)
% 42.54/42.76          | (r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 42.54/42.76          | (r2_hidden @ 
% 42.54/42.76             (sk_D @ X0 @ (k1_relat_1 @ X0) @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 42.54/42.76             (k10_relat_1 @ X0 @ X2))
% 42.54/42.76          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2))),
% 42.54/42.76      inference('sup-', [status(thm)], ['42', '51'])).
% 42.54/42.76  thf('53', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.54/42.76         (~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2)
% 42.54/42.76          | (r2_hidden @ 
% 42.54/42.76             (sk_D @ X0 @ (k1_relat_1 @ X0) @ (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 42.54/42.76             (k10_relat_1 @ X0 @ X2))
% 42.54/42.76          | ~ (v1_relat_1 @ X0)
% 42.54/42.76          | (r1_xboole_0 @ (k2_relat_1 @ X0) @ X1))),
% 42.54/42.76      inference('simplify', [status(thm)], ['52'])).
% 42.54/42.76  thf('54', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r1_xboole_0 @ (k2_relat_1 @ X1) @ X0)
% 42.54/42.76          | (r1_xboole_0 @ (k2_relat_1 @ X1) @ X0)
% 42.54/42.76          | ~ (v1_relat_1 @ X1)
% 42.54/42.76          | (r2_hidden @ 
% 42.54/42.76             (sk_D @ X1 @ (k1_relat_1 @ X1) @ (sk_C @ X0 @ (k2_relat_1 @ X1))) @ 
% 42.54/42.76             (k10_relat_1 @ X1 @ X0)))),
% 42.54/42.76      inference('sup-', [status(thm)], ['41', '53'])).
% 42.54/42.76  thf('55', plain,
% 42.54/42.76      (![X0 : $i, X1 : $i]:
% 42.54/42.76         ((r2_hidden @ 
% 42.54/42.76           (sk_D @ X1 @ (k1_relat_1 @ X1) @ (sk_C @ X0 @ (k2_relat_1 @ X1))) @ 
% 42.54/42.76           (k10_relat_1 @ X1 @ X0))
% 42.54/42.76          | ~ (v1_relat_1 @ X1)
% 42.54/42.76          | (r1_xboole_0 @ (k2_relat_1 @ X1) @ X0))),
% 42.54/42.76      inference('simplify', [status(thm)], ['54'])).
% 42.54/42.76  thf('56', plain,
% 42.54/42.76      (((r2_hidden @ 
% 42.54/42.76         (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ 
% 42.54/42.76          (sk_C @ sk_A @ (k2_relat_1 @ sk_B_1))) @ 
% 42.54/42.76         k1_xboole_0)
% 42.54/42.76        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)
% 42.54/42.76        | ~ (v1_relat_1 @ sk_B_1))),
% 42.54/42.76      inference('sup+', [status(thm)], ['40', '55'])).
% 42.54/42.76  thf('57', plain, ((v1_relat_1 @ sk_B_1)),
% 42.54/42.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.54/42.76  thf('58', plain,
% 42.54/42.76      (((r2_hidden @ 
% 42.54/42.76         (sk_D @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ 
% 42.54/42.76          (sk_C @ sk_A @ (k2_relat_1 @ sk_B_1))) @ 
% 42.54/42.76         k1_xboole_0)
% 42.54/42.76        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 42.54/42.76      inference('demod', [status(thm)], ['56', '57'])).
% 42.54/42.76  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 42.54/42.76  thf('59', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 42.54/42.76      inference('cnf', [status(esa)], [t65_xboole_1])).
% 42.54/42.76  thf(t55_zfmisc_1, axiom,
% 42.54/42.76    (![A:$i,B:$i,C:$i]:
% 42.54/42.76     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 42.54/42.76  thf('60', plain,
% 42.54/42.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 42.54/42.76         (~ (r1_xboole_0 @ (k2_tarski @ X20 @ X21) @ X22)
% 42.54/42.76          | ~ (r2_hidden @ X20 @ X22))),
% 42.54/42.76      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 42.54/42.76  thf('61', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 42.54/42.76      inference('sup-', [status(thm)], ['59', '60'])).
% 42.54/42.76  thf('62', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 42.54/42.76      inference('clc', [status(thm)], ['58', '61'])).
% 42.54/42.76  thf('63', plain, ($false), inference('demod', [status(thm)], ['36', '62'])).
% 42.54/42.76  
% 42.54/42.76  % SZS output end Refutation
% 42.54/42.76  
% 42.62/42.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
