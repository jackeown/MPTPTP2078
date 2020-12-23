%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.08DGhDmxNh

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:20 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 535 expanded)
%              Number of leaves         :   31 ( 168 expanded)
%              Depth                    :   22
%              Number of atoms          :  711 (5228 expanded)
%              Number of equality atoms :   59 ( 496 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ ( k2_tarski @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X37 ) )
      | ( X38
       != ( k1_funct_1 @ X37 @ X36 ) )
      | ( r2_hidden @ ( k4_tarski @ X36 @ X38 ) @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('9',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ( r2_hidden @ ( k4_tarski @ X36 @ ( k1_funct_1 @ X37 @ X36 ) ) @ X37 )
      | ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('14',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X33 @ X31 ) @ X32 )
      | ( r2_hidden @ X31 @ ( k11_relat_1 @ X32 @ X33 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k11_relat_1 @ X27 @ X28 )
        = ( k9_relat_1 @ X27 @ ( k1_tarski @ X28 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('21',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ( ( k7_relat_1 @ X34 @ X35 )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k9_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = ( k11_relat_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['19','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k11_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['15','16','29'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X26 @ X25 ) @ X25 )
      | ( X25
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = ( k11_relat_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('35',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k11_relat_1 @ X32 @ X33 ) )
      | ( r2_hidden @ ( k4_tarski @ X33 @ X31 ) @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X36 @ X38 ) @ X37 )
      | ( X38
        = ( k1_funct_1 @ X37 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
        = ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X36 @ X38 ) @ X37 )
      | ( X38
        = ( k1_funct_1 @ X37 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( sk_B @ ( k2_relat_1 @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) )
    | ( ( sk_B @ ( k2_relat_1 @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['15','16','29'])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('55',plain,(
    r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('57',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X36 @ X38 ) @ X37 )
      | ( X38
        = ( k1_funct_1 @ X37 @ X36 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( sk_B @ ( k2_relat_1 @ sk_B_1 ) )
      = ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( sk_B @ ( k2_relat_1 @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
        = ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','62'])).

thf('64',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( ( sk_C @ X26 @ X25 )
       != X26 )
      | ( X25
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k2_relat_1 @ sk_B_1 ) )
       != X0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B_1 )
      = ( k1_tarski @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_B @ ( k2_relat_1 @ sk_B_1 ) )
    = ( k1_funct_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('69',plain,(
    ( k2_relat_1 @ sk_B_1 )
 != ( k1_tarski @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['66','69'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['32','70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.08DGhDmxNh
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:14:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 330 iterations in 0.190s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.64  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.64  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.47/0.64  thf(t14_funct_1, conjecture,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.64       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.47/0.64         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i,B:$i]:
% 0.47/0.64        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.64          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.47/0.64            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.47/0.64  thf('0', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t69_enumset1, axiom,
% 0.47/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.64  thf('1', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.47/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.64  thf(d10_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.64  thf('3', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.47/0.64      inference('simplify', [status(thm)], ['2'])).
% 0.47/0.64  thf(t38_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.47/0.64       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.64         ((r2_hidden @ X21 @ X22)
% 0.47/0.64          | ~ (r1_tarski @ (k2_tarski @ X21 @ X23) @ X22))),
% 0.47/0.64      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.47/0.64  thf('5', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.64  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['1', '5'])).
% 0.47/0.64  thf('7', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['0', '6'])).
% 0.47/0.64  thf(t8_funct_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.64       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.47/0.64         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.47/0.64           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X36 @ (k1_relat_1 @ X37))
% 0.47/0.64          | ((X38) != (k1_funct_1 @ X37 @ X36))
% 0.47/0.64          | (r2_hidden @ (k4_tarski @ X36 @ X38) @ X37)
% 0.47/0.64          | ~ (v1_funct_1 @ X37)
% 0.47/0.64          | ~ (v1_relat_1 @ X37))),
% 0.47/0.64      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      (![X36 : $i, X37 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X37)
% 0.47/0.64          | ~ (v1_funct_1 @ X37)
% 0.47/0.64          | (r2_hidden @ (k4_tarski @ X36 @ (k1_funct_1 @ X37 @ X36)) @ X37)
% 0.47/0.64          | ~ (r2_hidden @ X36 @ (k1_relat_1 @ X37)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['8'])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B_1 @ sk_A)) @ sk_B_1)
% 0.47/0.64        | ~ (v1_funct_1 @ sk_B_1)
% 0.47/0.64        | ~ (v1_relat_1 @ sk_B_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['7', '9'])).
% 0.47/0.64  thf('11', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('12', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B_1 @ sk_A)) @ sk_B_1)),
% 0.47/0.64      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.47/0.64  thf(t204_relat_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ C ) =>
% 0.47/0.64       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.47/0.64         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.64         (~ (r2_hidden @ (k4_tarski @ X33 @ X31) @ X32)
% 0.47/0.64          | (r2_hidden @ X31 @ (k11_relat_1 @ X32 @ X33))
% 0.47/0.64          | ~ (v1_relat_1 @ X32))),
% 0.47/0.64      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      ((~ (v1_relat_1 @ sk_B_1)
% 0.47/0.64        | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ sk_A) @ 
% 0.47/0.64           (k11_relat_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.64  thf('16', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('17', plain, (((k1_relat_1 @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(d16_relat_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ A ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X27 : $i, X28 : $i]:
% 0.47/0.64         (((k11_relat_1 @ X27 @ X28) = (k9_relat_1 @ X27 @ (k1_tarski @ X28)))
% 0.47/0.64          | ~ (v1_relat_1 @ X27))),
% 0.47/0.64      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k11_relat_1 @ X0 @ sk_A)
% 0.47/0.64            = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B_1)))
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['17', '18'])).
% 0.47/0.64  thf('20', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.47/0.64      inference('simplify', [status(thm)], ['2'])).
% 0.47/0.64  thf(t97_relat_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ B ) =>
% 0.47/0.64       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.47/0.64         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      (![X34 : $i, X35 : $i]:
% 0.47/0.64         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 0.47/0.64          | ((k7_relat_1 @ X34 @ X35) = (X34))
% 0.47/0.64          | ~ (v1_relat_1 @ X34))),
% 0.47/0.64      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.64  thf(t148_relat_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ B ) =>
% 0.47/0.64       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.47/0.64  thf('23', plain,
% 0.47/0.64      (![X29 : $i, X30 : $i]:
% 0.47/0.64         (((k2_relat_1 @ (k7_relat_1 @ X29 @ X30)) = (k9_relat_1 @ X29 @ X30))
% 0.47/0.64          | ~ (v1_relat_1 @ X29))),
% 0.47/0.64      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (v1_relat_1 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['22', '23'])).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0)
% 0.47/0.64          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['24'])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      ((((k2_relat_1 @ sk_B_1) = (k11_relat_1 @ sk_B_1 @ sk_A))
% 0.47/0.64        | ~ (v1_relat_1 @ sk_B_1)
% 0.47/0.64        | ~ (v1_relat_1 @ sk_B_1))),
% 0.47/0.64      inference('sup+', [status(thm)], ['19', '25'])).
% 0.47/0.64  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('28', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('29', plain, (((k2_relat_1 @ sk_B_1) = (k11_relat_1 @ sk_B_1 @ sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.47/0.64      inference('demod', [status(thm)], ['15', '16', '29'])).
% 0.47/0.64  thf(d1_xboole_0, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.64  thf('32', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_B_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.64  thf(t41_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.47/0.64  thf('33', plain,
% 0.47/0.64      (![X25 : $i, X26 : $i]:
% 0.47/0.64         (((X25) = (k1_xboole_0))
% 0.47/0.64          | (r2_hidden @ (sk_C @ X26 @ X25) @ X25)
% 0.47/0.64          | ((X25) = (k1_tarski @ X26)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.47/0.64  thf('34', plain, (((k2_relat_1 @ sk_B_1) = (k11_relat_1 @ sk_B_1 @ sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.47/0.64  thf('35', plain,
% 0.47/0.64      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X31 @ (k11_relat_1 @ X32 @ X33))
% 0.47/0.64          | (r2_hidden @ (k4_tarski @ X33 @ X31) @ X32)
% 0.47/0.64          | ~ (v1_relat_1 @ X32))),
% 0.47/0.64      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.47/0.64          | ~ (v1_relat_1 @ sk_B_1)
% 0.47/0.64          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.64  thf('37', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.47/0.64          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B_1))),
% 0.47/0.64      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 0.47/0.64          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.47/0.64          | (r2_hidden @ 
% 0.47/0.64             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B_1))) @ sk_B_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['33', '38'])).
% 0.47/0.64  thf('40', plain,
% 0.47/0.64      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.64         (~ (r2_hidden @ (k4_tarski @ X36 @ X38) @ X37)
% 0.47/0.64          | ((X38) = (k1_funct_1 @ X37 @ X36))
% 0.47/0.64          | ~ (v1_funct_1 @ X37)
% 0.47/0.64          | ~ (v1_relat_1 @ X37))),
% 0.47/0.64      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.47/0.64          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 0.47/0.64          | ~ (v1_relat_1 @ sk_B_1)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_B_1)
% 0.47/0.64          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B_1)) = (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.64  thf('42', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('43', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('44', plain,
% 0.47/0.64      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.47/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.47/0.64          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B_1))),
% 0.47/0.64      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.64  thf('46', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_relat_1 @ sk_B_1))
% 0.47/0.64        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_B @ (k2_relat_1 @ sk_B_1))) @ 
% 0.47/0.64           sk_B_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.64         (~ (r2_hidden @ (k4_tarski @ X36 @ X38) @ X37)
% 0.47/0.64          | ((X38) = (k1_funct_1 @ X37 @ X36))
% 0.47/0.64          | ~ (v1_funct_1 @ X37)
% 0.47/0.64          | ~ (v1_relat_1 @ X37))),
% 0.47/0.64      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.47/0.64  thf('48', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_relat_1 @ sk_B_1))
% 0.47/0.64        | ~ (v1_relat_1 @ sk_B_1)
% 0.47/0.64        | ~ (v1_funct_1 @ sk_B_1)
% 0.47/0.64        | ((sk_B @ (k2_relat_1 @ sk_B_1)) = (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.64  thf('49', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('50', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      (((v1_xboole_0 @ (k2_relat_1 @ sk_B_1))
% 0.47/0.64        | ((sk_B @ (k2_relat_1 @ sk_B_1)) = (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.64      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ sk_A) @ (k2_relat_1 @ sk_B_1))),
% 0.47/0.64      inference('demod', [status(thm)], ['15', '16', '29'])).
% 0.47/0.64  thf('53', plain,
% 0.47/0.64      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_B_1)) @ (k2_relat_1 @ sk_B_1))
% 0.47/0.64        | (v1_xboole_0 @ (k2_relat_1 @ sk_B_1)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['51', '52'])).
% 0.47/0.64  thf('54', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_B_1))),
% 0.47/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      ((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_B_1)) @ (k2_relat_1 @ sk_B_1))),
% 0.47/0.64      inference('clc', [status(thm)], ['53', '54'])).
% 0.47/0.64  thf('56', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.47/0.64          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B_1))),
% 0.47/0.64      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.64  thf('57', plain,
% 0.47/0.64      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_B @ (k2_relat_1 @ sk_B_1))) @ 
% 0.47/0.64        sk_B_1)),
% 0.47/0.64      inference('sup-', [status(thm)], ['55', '56'])).
% 0.47/0.64  thf('58', plain,
% 0.47/0.64      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.64         (~ (r2_hidden @ (k4_tarski @ X36 @ X38) @ X37)
% 0.47/0.64          | ((X38) = (k1_funct_1 @ X37 @ X36))
% 0.47/0.64          | ~ (v1_funct_1 @ X37)
% 0.47/0.64          | ~ (v1_relat_1 @ X37))),
% 0.47/0.64      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.47/0.64  thf('59', plain,
% 0.47/0.64      ((~ (v1_relat_1 @ sk_B_1)
% 0.47/0.64        | ~ (v1_funct_1 @ sk_B_1)
% 0.47/0.64        | ((sk_B @ (k2_relat_1 @ sk_B_1)) = (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.47/0.64  thf('60', plain, ((v1_relat_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('61', plain, ((v1_funct_1 @ sk_B_1)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      (((sk_B @ (k2_relat_1 @ sk_B_1)) = (k1_funct_1 @ sk_B_1 @ sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.47/0.64  thf('63', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.47/0.64          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 0.47/0.64          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.47/0.64              = (sk_B @ (k2_relat_1 @ sk_B_1))))),
% 0.47/0.64      inference('demod', [status(thm)], ['41', '42', '43', '62'])).
% 0.47/0.64  thf('64', plain,
% 0.47/0.64      (![X25 : $i, X26 : $i]:
% 0.47/0.64         (((X25) = (k1_xboole_0))
% 0.47/0.64          | ((sk_C @ X26 @ X25) != (X26))
% 0.47/0.64          | ((X25) = (k1_tarski @ X26)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.47/0.64  thf('65', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((sk_B @ (k2_relat_1 @ sk_B_1)) != (X0))
% 0.47/0.64          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 0.47/0.64          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.47/0.64          | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ X0))
% 0.47/0.64          | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.64  thf('66', plain,
% 0.47/0.64      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0))
% 0.47/0.64        | ((k2_relat_1 @ sk_B_1) = (k1_tarski @ (sk_B @ (k2_relat_1 @ sk_B_1)))))),
% 0.47/0.64      inference('simplify', [status(thm)], ['65'])).
% 0.47/0.64  thf('67', plain,
% 0.47/0.64      (((k2_relat_1 @ sk_B_1) != (k1_tarski @ (k1_funct_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('68', plain,
% 0.47/0.64      (((sk_B @ (k2_relat_1 @ sk_B_1)) = (k1_funct_1 @ sk_B_1 @ sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.47/0.64  thf('69', plain,
% 0.47/0.64      (((k2_relat_1 @ sk_B_1) != (k1_tarski @ (sk_B @ (k2_relat_1 @ sk_B_1))))),
% 0.47/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.64  thf('70', plain, (((k2_relat_1 @ sk_B_1) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify_reflect-', [status(thm)], ['66', '69'])).
% 0.47/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.64  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.64  thf('72', plain, ($false),
% 0.47/0.64      inference('demod', [status(thm)], ['32', '70', '71'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
