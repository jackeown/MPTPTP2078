%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xUesrq8VOx

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:42 EST 2020

% Result     : Theorem 24.51s
% Output     : Refutation 24.51s
% Verified   : 
% Statistics : Number of formulae       :  171 (1256 expanded)
%              Number of leaves         :   41 ( 376 expanded)
%              Depth                    :   25
%              Number of atoms          : 1166 (10302 expanded)
%              Number of equality atoms :  122 (1559 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_8_type,type,(
    sk_C_8: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t23_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( C
            = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
         => ( ( ( k1_relat_1 @ C )
              = ( k1_tarski @ A ) )
            & ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relat_1])).

thf('0',plain,
    ( sk_C_8
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ( X24 != X25 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X25: $i] :
      ( r1_tarski @ X25 @ X25 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X92: $i,X93: $i] :
      ( ( r2_hidden @ X92 @ X93 )
      | ~ ( r1_tarski @ ( k1_tarski @ X92 ) @ X93 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B_2 ) @ sk_C_8 ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,
    ( sk_C_8
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X56: $i,X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X59 @ X58 )
      | ( X59 = X56 )
      | ( X58
       != ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X56: $i,X59: $i] :
      ( ( X59 = X56 )
      | ~ ( r2_hidden @ X59 @ ( k1_tarski @ X56 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('11',plain,(
    ! [X82: $i,X83: $i] :
      ( ( X83 != X82 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X83 ) @ ( k1_tarski @ X82 ) )
       != ( k1_tarski @ X83 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('12',plain,(
    ! [X82: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X82 ) @ ( k1_tarski @ X82 ) )
     != ( k1_tarski @ X82 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X27: $i] :
      ( ( k2_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k4_xboole_0 @ X47 @ ( k2_xboole_0 @ X47 @ X48 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X82: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X82 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['10','16'])).

thf('18',plain,
    ( ( sk_B_1 @ sk_C_8 )
    = ( k4_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['6','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_B_1 @ sk_C_8 ) @ sk_C_8 ),
    inference(demod,[status(thm)],['5','18'])).

thf('20',plain,
    ( sk_C_8
    = ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B_1 @ sk_C_8 )
    = ( k4_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['6','17'])).

thf('22',plain,
    ( sk_C_8
    = ( k1_tarski @ ( sk_B_1 @ sk_C_8 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X56: $i,X59: $i] :
      ( ( X59 = X56 )
      | ~ ( r2_hidden @ X59 @ ( k1_tarski @ X56 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X69: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X69 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B @ sk_C_8 )
    = ( sk_B_1 @ sk_C_8 ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_B @ sk_C_8 ) @ sk_C_8 ),
    inference(demod,[status(thm)],['19','28'])).

thf('30',plain,
    ( sk_C_8
    = ( k1_tarski @ ( sk_B_1 @ sk_C_8 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('31',plain,
    ( ( sk_B @ sk_C_8 )
    = ( sk_B_1 @ sk_C_8 ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('32',plain,
    ( sk_C_8
    = ( k1_tarski @ ( sk_B @ sk_C_8 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X83: $i,X84: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X83 ) @ ( k1_tarski @ X84 ) )
        = ( k1_tarski @ X83 ) )
      | ( X83 = X84 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('34',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k2_tarski @ X61 @ X62 )
      = ( k2_xboole_0 @ ( k1_tarski @ X61 ) @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X36 @ X37 ) @ X37 )
      = ( k4_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k2_tarski @ X61 @ X62 )
      = ( k2_xboole_0 @ ( k1_tarski @ X61 ) @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k2_tarski @ X61 @ X62 )
      = ( k2_xboole_0 @ ( k1_tarski @ X61 ) @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('42',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X70 @ X71 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X70 @ X72 ) @ X71 )
       != ( k1_tarski @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( '#_fresh_sk1' @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(inj_rec,[status(thm)],['47'])).

thf('49',plain,
    ( ( '#_fresh_sk1' @ sk_C_8 )
    = ( sk_B @ sk_C_8 ) ),
    inference('sup+',[status(thm)],['32','48'])).

thf('50',plain,(
    r2_hidden @ ( '#_fresh_sk1' @ sk_C_8 ) @ sk_C_8 ),
    inference(demod,[status(thm)],['29','49'])).

thf('51',plain,
    ( ( sk_B_1 @ sk_C_8 )
    = ( k4_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['6','17'])).

thf('52',plain,
    ( ( sk_B @ sk_C_8 )
    = ( sk_B_1 @ sk_C_8 ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('53',plain,
    ( ( sk_B @ sk_C_8 )
    = ( k4_tarski @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( '#_fresh_sk1' @ sk_C_8 )
    = ( sk_B @ sk_C_8 ) ),
    inference('sup+',[status(thm)],['32','48'])).

thf('55',plain,
    ( ( '#_fresh_sk1' @ sk_C_8 )
    = ( k4_tarski @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('56',plain,(
    ! [X113: $i,X114: $i,X115: $i,X116: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X113 @ X114 ) @ X115 )
      | ( r2_hidden @ X114 @ X116 )
      | ( X116
       != ( k2_relat_1 @ X115 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('57',plain,(
    ! [X113: $i,X114: $i,X115: $i] :
      ( ( r2_hidden @ X114 @ ( k2_relat_1 @ X115 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X113 @ X114 ) @ X115 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( '#_fresh_sk1' @ sk_C_8 ) @ X0 )
      | ( r2_hidden @ sk_B_2 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    r2_hidden @ sk_B_2 @ ( k2_relat_1 @ sk_C_8 ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    ! [X92: $i,X94: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X92 ) @ X94 )
      | ~ ( r2_hidden @ X92 @ X94 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('61',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_2 ) @ ( k2_relat_1 @ sk_C_8 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X24: $i,X26: $i] :
      ( ( X24 = X26 )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_8 ) @ ( k1_tarski @ sk_B_2 ) )
    | ( ( k2_relat_1 @ sk_C_8 )
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('65',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,(
    ! [X115: $i,X116: $i,X117: $i] :
      ( ~ ( r2_hidden @ X117 @ X116 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X117 @ X115 ) @ X117 ) @ X115 )
      | ( X116
       != ( k2_relat_1 @ X115 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('67',plain,(
    ! [X115: $i,X117: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X117 @ X115 ) @ X117 ) @ X115 )
      | ~ ( r2_hidden @ X117 @ ( k2_relat_1 @ X115 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,
    ( ( '#_fresh_sk1' @ sk_C_8 )
    = ( k4_tarski @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('70',plain,(
    ! [X85: $i,X86: $i,X87: $i,X88: $i] :
      ( ( X87 = X88 )
      | ~ ( r2_hidden @ ( k4_tarski @ X86 @ X87 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X85 ) @ ( k1_tarski @ X88 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('71',plain,(
    ! [X90: $i,X91: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X90 ) @ ( k1_tarski @ X91 ) )
      = ( k1_tarski @ ( k4_tarski @ X90 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('72',plain,(
    ! [X85: $i,X86: $i,X87: $i,X88: $i] :
      ( ( X87 = X88 )
      | ~ ( r2_hidden @ ( k4_tarski @ X86 @ X87 ) @ ( k1_tarski @ ( k4_tarski @ X85 @ X88 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_tarski @ ( '#_fresh_sk1' @ sk_C_8 ) ) )
      | ( X0 = sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( sk_C_8
    = ( k1_tarski @ ( sk_B @ sk_C_8 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('75',plain,
    ( ( '#_fresh_sk1' @ sk_C_8 )
    = ( sk_B @ sk_C_8 ) ),
    inference('sup+',[status(thm)],['32','48'])).

thf('76',plain,
    ( sk_C_8
    = ( k1_tarski @ ( '#_fresh_sk1' @ sk_C_8 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_8 )
      | ( X0 = sk_B_2 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_8 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_8 ) )
        = sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['68','77'])).

thf('79',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_2 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_8 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_8 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_8 ) @ X0 )
      | ~ ( r2_hidden @ sk_B_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_8 ) @ ( k1_tarski @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['64','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C_8 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(demod,[status(thm)],['63','82'])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C_8 )
     != ( k1_tarski @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C_8 )
     != ( k1_tarski @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k2_relat_1 @ sk_C_8 )
     != ( k1_tarski @ sk_B_2 ) )
   <= ( ( k2_relat_1 @ sk_C_8 )
     != ( k1_tarski @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,(
    r2_hidden @ ( sk_B @ sk_C_8 ) @ sk_C_8 ),
    inference(demod,[status(thm)],['19','28'])).

thf('87',plain,
    ( ( sk_B @ sk_C_8 )
    = ( k4_tarski @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('88',plain,(
    ! [X106: $i,X107: $i,X108: $i,X109: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X106 @ X107 ) @ X108 )
      | ( r2_hidden @ X106 @ X109 )
      | ( X109
       != ( k1_relat_1 @ X108 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('89',plain,(
    ! [X106: $i,X107: $i,X108: $i] :
      ( ( r2_hidden @ X106 @ ( k1_relat_1 @ X108 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X106 @ X107 ) @ X108 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ sk_C_8 ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_8 ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,(
    ! [X92: $i,X94: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X92 ) @ X94 )
      | ~ ( r2_hidden @ X92 @ X94 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('93',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_C_8 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X24: $i,X26: $i] :
      ( ( X24 = X26 )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('95',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_8 ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_8 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('97',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,(
    ! [X108: $i,X109: $i,X110: $i] :
      ( ~ ( r2_hidden @ X110 @ X109 )
      | ( r2_hidden @ ( k4_tarski @ X110 @ ( sk_D_2 @ X110 @ X108 ) ) @ X108 )
      | ( X109
       != ( k1_relat_1 @ X108 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('99',plain,(
    ! [X108: $i,X110: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X110 @ ( sk_D_2 @ X110 @ X108 ) ) @ X108 )
      | ~ ( r2_hidden @ X110 @ ( k1_relat_1 @ X108 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_2 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_8 ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('102',plain,(
    ! [X108: $i,X110: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X110 @ ( sk_D_2 @ X110 @ X108 ) ) @ X108 )
      | ~ ( r2_hidden @ X110 @ ( k1_relat_1 @ X108 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('103',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_C_8 ) ) @ sk_C_8 ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( sk_C_8
    = ( k1_tarski @ ( sk_B @ sk_C_8 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('105',plain,(
    ! [X56: $i,X59: $i] :
      ( ( X59 = X56 )
      | ~ ( r2_hidden @ X59 @ ( k1_tarski @ X56 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_8 )
      | ( X0
        = ( sk_B @ sk_C_8 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_C_8 ) )
    = ( sk_B @ sk_C_8 ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( '#_fresh_sk1' @ sk_C_8 )
    = ( sk_B @ sk_C_8 ) ),
    inference('sup+',[status(thm)],['32','48'])).

thf('109',plain,
    ( ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_C_8 ) )
    = ( '#_fresh_sk1' @ sk_C_8 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X85: $i,X86: $i,X87: $i,X88: $i] :
      ( ( X86 = X85 )
      | ~ ( r2_hidden @ ( k4_tarski @ X86 @ X87 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X85 ) @ ( k1_tarski @ X88 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('111',plain,(
    ! [X90: $i,X91: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X90 ) @ ( k1_tarski @ X91 ) )
      = ( k1_tarski @ ( k4_tarski @ X90 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('112',plain,(
    ! [X85: $i,X86: $i,X87: $i,X88: $i] :
      ( ( X86 = X85 )
      | ~ ( r2_hidden @ ( k4_tarski @ X86 @ X87 ) @ ( k1_tarski @ ( k4_tarski @ X85 @ X88 ) ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k1_tarski @ ( '#_fresh_sk1' @ sk_C_8 ) ) )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,
    ( sk_C_8
    = ( k1_tarski @ ( '#_fresh_sk1' @ sk_C_8 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_8 )
      | ( X1 = sk_A ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_8 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_8 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['100','115'])).

thf('117',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_8 ) @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_8 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_8 ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_8 ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['96','119'])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_C_8 )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['95','120'])).

thf('122',plain,
    ( ( ( k1_relat_1 @ sk_C_8 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_C_8 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['84'])).

thf('123',plain,
    ( ( ( k1_relat_1 @ sk_C_8 )
     != ( k1_relat_1 @ sk_C_8 ) )
   <= ( ( k1_relat_1 @ sk_C_8 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k1_relat_1 @ sk_C_8 )
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( ( k2_relat_1 @ sk_C_8 )
     != ( k1_tarski @ sk_B_2 ) )
    | ( ( k1_relat_1 @ sk_C_8 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['84'])).

thf('126',plain,(
    ( k2_relat_1 @ sk_C_8 )
 != ( k1_tarski @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['124','125'])).

thf('127',plain,(
    ( k2_relat_1 @ sk_C_8 )
 != ( k1_tarski @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['85','126'])).

thf('128',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['83','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xUesrq8VOx
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 24.51/24.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 24.51/24.70  % Solved by: fo/fo7.sh
% 24.51/24.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.51/24.70  % done 28102 iterations in 24.212s
% 24.51/24.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 24.51/24.70  % SZS output start Refutation
% 24.51/24.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 24.51/24.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 24.51/24.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 24.51/24.70  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 24.51/24.70  thf(sk_B_2_type, type, sk_B_2: $i).
% 24.51/24.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 24.51/24.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 24.51/24.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 24.51/24.70  thf(sk_B_type, type, sk_B: $i > $i).
% 24.51/24.70  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 24.51/24.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 24.51/24.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 24.51/24.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 24.51/24.70  thf(sk_C_8_type, type, sk_C_8: $i).
% 24.51/24.70  thf(sk_A_type, type, sk_A: $i).
% 24.51/24.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 24.51/24.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 24.51/24.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 24.51/24.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 24.51/24.70  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 24.51/24.70  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 24.51/24.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 24.51/24.70  thf(t23_relat_1, conjecture,
% 24.51/24.70    (![A:$i,B:$i,C:$i]:
% 24.51/24.70     ( ( v1_relat_1 @ C ) =>
% 24.51/24.70       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 24.51/24.70         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 24.51/24.70           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 24.51/24.70  thf(zf_stmt_0, negated_conjecture,
% 24.51/24.70    (~( ![A:$i,B:$i,C:$i]:
% 24.51/24.70        ( ( v1_relat_1 @ C ) =>
% 24.51/24.70          ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 24.51/24.70            ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 24.51/24.70              ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ) )),
% 24.51/24.70    inference('cnf.neg', [status(esa)], [t23_relat_1])).
% 24.51/24.70  thf('0', plain, (((sk_C_8) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B_2)))),
% 24.51/24.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.70  thf(d10_xboole_0, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 24.51/24.70  thf('1', plain,
% 24.51/24.70      (![X24 : $i, X25 : $i]: ((r1_tarski @ X24 @ X25) | ((X24) != (X25)))),
% 24.51/24.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.51/24.70  thf('2', plain, (![X25 : $i]: (r1_tarski @ X25 @ X25)),
% 24.51/24.70      inference('simplify', [status(thm)], ['1'])).
% 24.51/24.70  thf(t37_zfmisc_1, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 24.51/24.70  thf('3', plain,
% 24.51/24.70      (![X92 : $i, X93 : $i]:
% 24.51/24.70         ((r2_hidden @ X92 @ X93) | ~ (r1_tarski @ (k1_tarski @ X92) @ X93))),
% 24.51/24.70      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 24.51/24.70  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 24.51/24.70      inference('sup-', [status(thm)], ['2', '3'])).
% 24.51/24.70  thf('5', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B_2) @ sk_C_8)),
% 24.51/24.70      inference('sup+', [status(thm)], ['0', '4'])).
% 24.51/24.70  thf('6', plain, (((sk_C_8) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B_2)))),
% 24.51/24.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.70  thf(t7_xboole_0, axiom,
% 24.51/24.70    (![A:$i]:
% 24.51/24.70     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 24.51/24.70          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 24.51/24.70  thf('7', plain,
% 24.51/24.70      (![X23 : $i]:
% 24.51/24.70         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X23) @ X23))),
% 24.51/24.70      inference('cnf', [status(esa)], [t7_xboole_0])).
% 24.51/24.70  thf(d1_tarski, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 24.51/24.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 24.51/24.70  thf('8', plain,
% 24.51/24.70      (![X56 : $i, X58 : $i, X59 : $i]:
% 24.51/24.70         (~ (r2_hidden @ X59 @ X58)
% 24.51/24.70          | ((X59) = (X56))
% 24.51/24.70          | ((X58) != (k1_tarski @ X56)))),
% 24.51/24.70      inference('cnf', [status(esa)], [d1_tarski])).
% 24.51/24.70  thf('9', plain,
% 24.51/24.70      (![X56 : $i, X59 : $i]:
% 24.51/24.70         (((X59) = (X56)) | ~ (r2_hidden @ X59 @ (k1_tarski @ X56)))),
% 24.51/24.70      inference('simplify', [status(thm)], ['8'])).
% 24.51/24.70  thf('10', plain,
% 24.51/24.70      (![X0 : $i]:
% 24.51/24.70         (((k1_tarski @ X0) = (k1_xboole_0))
% 24.51/24.70          | ((sk_B_1 @ (k1_tarski @ X0)) = (X0)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['7', '9'])).
% 24.51/24.70  thf(t20_zfmisc_1, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 24.51/24.70         ( k1_tarski @ A ) ) <=>
% 24.51/24.70       ( ( A ) != ( B ) ) ))).
% 24.51/24.70  thf('11', plain,
% 24.51/24.70      (![X82 : $i, X83 : $i]:
% 24.51/24.70         (((X83) != (X82))
% 24.51/24.70          | ((k4_xboole_0 @ (k1_tarski @ X83) @ (k1_tarski @ X82))
% 24.51/24.70              != (k1_tarski @ X83)))),
% 24.51/24.70      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 24.51/24.70  thf('12', plain,
% 24.51/24.70      (![X82 : $i]:
% 24.51/24.70         ((k4_xboole_0 @ (k1_tarski @ X82) @ (k1_tarski @ X82))
% 24.51/24.70           != (k1_tarski @ X82))),
% 24.51/24.70      inference('simplify', [status(thm)], ['11'])).
% 24.51/24.70  thf(t1_boole, axiom,
% 24.51/24.70    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 24.51/24.70  thf('13', plain, (![X27 : $i]: ((k2_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 24.51/24.70      inference('cnf', [status(esa)], [t1_boole])).
% 24.51/24.70  thf(t46_xboole_1, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 24.51/24.70  thf('14', plain,
% 24.51/24.70      (![X47 : $i, X48 : $i]:
% 24.51/24.70         ((k4_xboole_0 @ X47 @ (k2_xboole_0 @ X47 @ X48)) = (k1_xboole_0))),
% 24.51/24.70      inference('cnf', [status(esa)], [t46_xboole_1])).
% 24.51/24.70  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 24.51/24.70      inference('sup+', [status(thm)], ['13', '14'])).
% 24.51/24.70  thf('16', plain, (![X82 : $i]: ((k1_xboole_0) != (k1_tarski @ X82))),
% 24.51/24.70      inference('demod', [status(thm)], ['12', '15'])).
% 24.51/24.70  thf('17', plain, (![X0 : $i]: ((sk_B_1 @ (k1_tarski @ X0)) = (X0))),
% 24.51/24.70      inference('clc', [status(thm)], ['10', '16'])).
% 24.51/24.70  thf('18', plain, (((sk_B_1 @ sk_C_8) = (k4_tarski @ sk_A @ sk_B_2))),
% 24.51/24.70      inference('sup+', [status(thm)], ['6', '17'])).
% 24.51/24.70  thf('19', plain, ((r2_hidden @ (sk_B_1 @ sk_C_8) @ sk_C_8)),
% 24.51/24.70      inference('demod', [status(thm)], ['5', '18'])).
% 24.51/24.70  thf('20', plain, (((sk_C_8) = (k1_tarski @ (k4_tarski @ sk_A @ sk_B_2)))),
% 24.51/24.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.70  thf('21', plain, (((sk_B_1 @ sk_C_8) = (k4_tarski @ sk_A @ sk_B_2))),
% 24.51/24.70      inference('sup+', [status(thm)], ['6', '17'])).
% 24.51/24.70  thf('22', plain, (((sk_C_8) = (k1_tarski @ (sk_B_1 @ sk_C_8)))),
% 24.51/24.70      inference('demod', [status(thm)], ['20', '21'])).
% 24.51/24.70  thf(d1_xboole_0, axiom,
% 24.51/24.70    (![A:$i]:
% 24.51/24.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 24.51/24.70  thf('23', plain,
% 24.51/24.70      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 24.51/24.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 24.51/24.70  thf('24', plain,
% 24.51/24.70      (![X56 : $i, X59 : $i]:
% 24.51/24.70         (((X59) = (X56)) | ~ (r2_hidden @ X59 @ (k1_tarski @ X56)))),
% 24.51/24.70      inference('simplify', [status(thm)], ['8'])).
% 24.51/24.70  thf('25', plain,
% 24.51/24.70      (![X0 : $i]:
% 24.51/24.70         ((v1_xboole_0 @ (k1_tarski @ X0)) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['23', '24'])).
% 24.51/24.70  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 24.51/24.70  thf('26', plain, (![X69 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X69))),
% 24.51/24.70      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 24.51/24.70  thf('27', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 24.51/24.70      inference('clc', [status(thm)], ['25', '26'])).
% 24.51/24.70  thf('28', plain, (((sk_B @ sk_C_8) = (sk_B_1 @ sk_C_8))),
% 24.51/24.70      inference('sup+', [status(thm)], ['22', '27'])).
% 24.51/24.70  thf('29', plain, ((r2_hidden @ (sk_B @ sk_C_8) @ sk_C_8)),
% 24.51/24.70      inference('demod', [status(thm)], ['19', '28'])).
% 24.51/24.70  thf('30', plain, (((sk_C_8) = (k1_tarski @ (sk_B_1 @ sk_C_8)))),
% 24.51/24.70      inference('demod', [status(thm)], ['20', '21'])).
% 24.51/24.70  thf('31', plain, (((sk_B @ sk_C_8) = (sk_B_1 @ sk_C_8))),
% 24.51/24.70      inference('sup+', [status(thm)], ['22', '27'])).
% 24.51/24.70  thf('32', plain, (((sk_C_8) = (k1_tarski @ (sk_B @ sk_C_8)))),
% 24.51/24.70      inference('demod', [status(thm)], ['30', '31'])).
% 24.51/24.70  thf('33', plain,
% 24.51/24.70      (![X83 : $i, X84 : $i]:
% 24.51/24.70         (((k4_xboole_0 @ (k1_tarski @ X83) @ (k1_tarski @ X84))
% 24.51/24.70            = (k1_tarski @ X83))
% 24.51/24.70          | ((X83) = (X84)))),
% 24.51/24.70      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 24.51/24.70  thf(t41_enumset1, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( k2_tarski @ A @ B ) =
% 24.51/24.70       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 24.51/24.70  thf('34', plain,
% 24.51/24.70      (![X61 : $i, X62 : $i]:
% 24.51/24.70         ((k2_tarski @ X61 @ X62)
% 24.51/24.70           = (k2_xboole_0 @ (k1_tarski @ X61) @ (k1_tarski @ X62)))),
% 24.51/24.70      inference('cnf', [status(esa)], [t41_enumset1])).
% 24.51/24.70  thf(t40_xboole_1, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 24.51/24.70  thf('35', plain,
% 24.51/24.70      (![X36 : $i, X37 : $i]:
% 24.51/24.70         ((k4_xboole_0 @ (k2_xboole_0 @ X36 @ X37) @ X37)
% 24.51/24.70           = (k4_xboole_0 @ X36 @ X37))),
% 24.51/24.70      inference('cnf', [status(esa)], [t40_xboole_1])).
% 24.51/24.70  thf('36', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         ((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 24.51/24.70           = (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 24.51/24.70      inference('sup+', [status(thm)], ['34', '35'])).
% 24.51/24.70  thf('37', plain,
% 24.51/24.70      (![X61 : $i, X62 : $i]:
% 24.51/24.70         ((k2_tarski @ X61 @ X62)
% 24.51/24.70           = (k2_xboole_0 @ (k1_tarski @ X61) @ (k1_tarski @ X62)))),
% 24.51/24.70      inference('cnf', [status(esa)], [t41_enumset1])).
% 24.51/24.70  thf(commutativity_k2_xboole_0, axiom,
% 24.51/24.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 24.51/24.70  thf('38', plain,
% 24.51/24.70      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 24.51/24.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 24.51/24.70  thf('39', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 24.51/24.70           = (k2_tarski @ X1 @ X0))),
% 24.51/24.70      inference('sup+', [status(thm)], ['37', '38'])).
% 24.51/24.70  thf('40', plain,
% 24.51/24.70      (![X61 : $i, X62 : $i]:
% 24.51/24.70         ((k2_tarski @ X61 @ X62)
% 24.51/24.70           = (k2_xboole_0 @ (k1_tarski @ X61) @ (k1_tarski @ X62)))),
% 24.51/24.70      inference('cnf', [status(esa)], [t41_enumset1])).
% 24.51/24.70  thf('41', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 24.51/24.70      inference('sup+', [status(thm)], ['39', '40'])).
% 24.51/24.70  thf(l38_zfmisc_1, axiom,
% 24.51/24.70    (![A:$i,B:$i,C:$i]:
% 24.51/24.70     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 24.51/24.70       ( ( ~( r2_hidden @ A @ C ) ) & 
% 24.51/24.70         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 24.51/24.70  thf('42', plain,
% 24.51/24.70      (![X70 : $i, X71 : $i, X72 : $i]:
% 24.51/24.70         (~ (r2_hidden @ X70 @ X71)
% 24.51/24.70          | ((k4_xboole_0 @ (k2_tarski @ X70 @ X72) @ X71) != (k1_tarski @ X70)))),
% 24.51/24.70      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 24.51/24.70  thf('43', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.51/24.70         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) != (k1_tarski @ X0))
% 24.51/24.70          | ~ (r2_hidden @ X0 @ X2))),
% 24.51/24.70      inference('sup-', [status(thm)], ['41', '42'])).
% 24.51/24.70  thf('44', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         (((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 24.51/24.70            != (k1_tarski @ X0))
% 24.51/24.70          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['36', '43'])).
% 24.51/24.70  thf('45', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 24.51/24.70      inference('sup-', [status(thm)], ['2', '3'])).
% 24.51/24.70  thf('46', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 24.51/24.70           != (k1_tarski @ X0))),
% 24.51/24.70      inference('demod', [status(thm)], ['44', '45'])).
% 24.51/24.70  thf('47', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         (((k1_tarski @ X0) != (k1_tarski @ X1)) | ((X0) = (X1)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['33', '46'])).
% 24.51/24.70  thf('48', plain, (![X0 : $i]: (('#_fresh_sk1' @ (k1_tarski @ X0)) = (X0))),
% 24.51/24.70      inference('inj_rec', [status(thm)], ['47'])).
% 24.51/24.70  thf('49', plain, ((('#_fresh_sk1' @ sk_C_8) = (sk_B @ sk_C_8))),
% 24.51/24.70      inference('sup+', [status(thm)], ['32', '48'])).
% 24.51/24.70  thf('50', plain, ((r2_hidden @ ('#_fresh_sk1' @ sk_C_8) @ sk_C_8)),
% 24.51/24.70      inference('demod', [status(thm)], ['29', '49'])).
% 24.51/24.70  thf('51', plain, (((sk_B_1 @ sk_C_8) = (k4_tarski @ sk_A @ sk_B_2))),
% 24.51/24.70      inference('sup+', [status(thm)], ['6', '17'])).
% 24.51/24.70  thf('52', plain, (((sk_B @ sk_C_8) = (sk_B_1 @ sk_C_8))),
% 24.51/24.70      inference('sup+', [status(thm)], ['22', '27'])).
% 24.51/24.70  thf('53', plain, (((sk_B @ sk_C_8) = (k4_tarski @ sk_A @ sk_B_2))),
% 24.51/24.70      inference('demod', [status(thm)], ['51', '52'])).
% 24.51/24.70  thf('54', plain, ((('#_fresh_sk1' @ sk_C_8) = (sk_B @ sk_C_8))),
% 24.51/24.70      inference('sup+', [status(thm)], ['32', '48'])).
% 24.51/24.70  thf('55', plain, ((('#_fresh_sk1' @ sk_C_8) = (k4_tarski @ sk_A @ sk_B_2))),
% 24.51/24.70      inference('demod', [status(thm)], ['53', '54'])).
% 24.51/24.70  thf(d5_relat_1, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 24.51/24.70       ( ![C:$i]:
% 24.51/24.70         ( ( r2_hidden @ C @ B ) <=>
% 24.51/24.70           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 24.51/24.70  thf('56', plain,
% 24.51/24.70      (![X113 : $i, X114 : $i, X115 : $i, X116 : $i]:
% 24.51/24.70         (~ (r2_hidden @ (k4_tarski @ X113 @ X114) @ X115)
% 24.51/24.70          | (r2_hidden @ X114 @ X116)
% 24.51/24.70          | ((X116) != (k2_relat_1 @ X115)))),
% 24.51/24.70      inference('cnf', [status(esa)], [d5_relat_1])).
% 24.51/24.70  thf('57', plain,
% 24.51/24.70      (![X113 : $i, X114 : $i, X115 : $i]:
% 24.51/24.70         ((r2_hidden @ X114 @ (k2_relat_1 @ X115))
% 24.51/24.70          | ~ (r2_hidden @ (k4_tarski @ X113 @ X114) @ X115))),
% 24.51/24.70      inference('simplify', [status(thm)], ['56'])).
% 24.51/24.70  thf('58', plain,
% 24.51/24.70      (![X0 : $i]:
% 24.51/24.70         (~ (r2_hidden @ ('#_fresh_sk1' @ sk_C_8) @ X0)
% 24.51/24.70          | (r2_hidden @ sk_B_2 @ (k2_relat_1 @ X0)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['55', '57'])).
% 24.51/24.70  thf('59', plain, ((r2_hidden @ sk_B_2 @ (k2_relat_1 @ sk_C_8))),
% 24.51/24.70      inference('sup-', [status(thm)], ['50', '58'])).
% 24.51/24.70  thf('60', plain,
% 24.51/24.70      (![X92 : $i, X94 : $i]:
% 24.51/24.70         ((r1_tarski @ (k1_tarski @ X92) @ X94) | ~ (r2_hidden @ X92 @ X94))),
% 24.51/24.70      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 24.51/24.70  thf('61', plain,
% 24.51/24.70      ((r1_tarski @ (k1_tarski @ sk_B_2) @ (k2_relat_1 @ sk_C_8))),
% 24.51/24.70      inference('sup-', [status(thm)], ['59', '60'])).
% 24.51/24.70  thf('62', plain,
% 24.51/24.70      (![X24 : $i, X26 : $i]:
% 24.51/24.70         (((X24) = (X26))
% 24.51/24.70          | ~ (r1_tarski @ X26 @ X24)
% 24.51/24.70          | ~ (r1_tarski @ X24 @ X26))),
% 24.51/24.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.51/24.70  thf('63', plain,
% 24.51/24.70      ((~ (r1_tarski @ (k2_relat_1 @ sk_C_8) @ (k1_tarski @ sk_B_2))
% 24.51/24.70        | ((k2_relat_1 @ sk_C_8) = (k1_tarski @ sk_B_2)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['61', '62'])).
% 24.51/24.70  thf('64', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 24.51/24.70      inference('sup-', [status(thm)], ['2', '3'])).
% 24.51/24.70  thf(d3_tarski, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( r1_tarski @ A @ B ) <=>
% 24.51/24.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 24.51/24.70  thf('65', plain,
% 24.51/24.70      (![X8 : $i, X10 : $i]:
% 24.51/24.70         ((r1_tarski @ X8 @ X10) | (r2_hidden @ (sk_C @ X10 @ X8) @ X8))),
% 24.51/24.70      inference('cnf', [status(esa)], [d3_tarski])).
% 24.51/24.70  thf('66', plain,
% 24.51/24.70      (![X115 : $i, X116 : $i, X117 : $i]:
% 24.51/24.70         (~ (r2_hidden @ X117 @ X116)
% 24.51/24.70          | (r2_hidden @ (k4_tarski @ (sk_D_4 @ X117 @ X115) @ X117) @ X115)
% 24.51/24.70          | ((X116) != (k2_relat_1 @ X115)))),
% 24.51/24.70      inference('cnf', [status(esa)], [d5_relat_1])).
% 24.51/24.70  thf('67', plain,
% 24.51/24.70      (![X115 : $i, X117 : $i]:
% 24.51/24.70         ((r2_hidden @ (k4_tarski @ (sk_D_4 @ X117 @ X115) @ X117) @ X115)
% 24.51/24.70          | ~ (r2_hidden @ X117 @ (k2_relat_1 @ X115)))),
% 24.51/24.70      inference('simplify', [status(thm)], ['66'])).
% 24.51/24.70  thf('68', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 24.51/24.70          | (r2_hidden @ 
% 24.51/24.70             (k4_tarski @ (sk_D_4 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 24.51/24.70              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 24.51/24.70             X0))),
% 24.51/24.70      inference('sup-', [status(thm)], ['65', '67'])).
% 24.51/24.70  thf('69', plain, ((('#_fresh_sk1' @ sk_C_8) = (k4_tarski @ sk_A @ sk_B_2))),
% 24.51/24.70      inference('demod', [status(thm)], ['53', '54'])).
% 24.51/24.70  thf(t34_zfmisc_1, axiom,
% 24.51/24.70    (![A:$i,B:$i,C:$i,D:$i]:
% 24.51/24.70     ( ( r2_hidden @
% 24.51/24.70         ( k4_tarski @ A @ B ) @ 
% 24.51/24.70         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 24.51/24.70       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 24.51/24.70  thf('70', plain,
% 24.51/24.70      (![X85 : $i, X86 : $i, X87 : $i, X88 : $i]:
% 24.51/24.70         (((X87) = (X88))
% 24.51/24.70          | ~ (r2_hidden @ (k4_tarski @ X86 @ X87) @ 
% 24.51/24.70               (k2_zfmisc_1 @ (k1_tarski @ X85) @ (k1_tarski @ X88))))),
% 24.51/24.70      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 24.51/24.70  thf(t35_zfmisc_1, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 24.51/24.70       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 24.51/24.70  thf('71', plain,
% 24.51/24.70      (![X90 : $i, X91 : $i]:
% 24.51/24.70         ((k2_zfmisc_1 @ (k1_tarski @ X90) @ (k1_tarski @ X91))
% 24.51/24.70           = (k1_tarski @ (k4_tarski @ X90 @ X91)))),
% 24.51/24.70      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 24.51/24.70  thf('72', plain,
% 24.51/24.70      (![X85 : $i, X86 : $i, X87 : $i, X88 : $i]:
% 24.51/24.70         (((X87) = (X88))
% 24.51/24.70          | ~ (r2_hidden @ (k4_tarski @ X86 @ X87) @ 
% 24.51/24.70               (k1_tarski @ (k4_tarski @ X85 @ X88))))),
% 24.51/24.70      inference('demod', [status(thm)], ['70', '71'])).
% 24.51/24.70  thf('73', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 24.51/24.70             (k1_tarski @ ('#_fresh_sk1' @ sk_C_8)))
% 24.51/24.70          | ((X0) = (sk_B_2)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['69', '72'])).
% 24.51/24.70  thf('74', plain, (((sk_C_8) = (k1_tarski @ (sk_B @ sk_C_8)))),
% 24.51/24.70      inference('demod', [status(thm)], ['30', '31'])).
% 24.51/24.70  thf('75', plain, ((('#_fresh_sk1' @ sk_C_8) = (sk_B @ sk_C_8))),
% 24.51/24.70      inference('sup+', [status(thm)], ['32', '48'])).
% 24.51/24.70  thf('76', plain, (((sk_C_8) = (k1_tarski @ ('#_fresh_sk1' @ sk_C_8)))),
% 24.51/24.70      inference('demod', [status(thm)], ['74', '75'])).
% 24.51/24.70  thf('77', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_8) | ((X0) = (sk_B_2)))),
% 24.51/24.70      inference('demod', [status(thm)], ['73', '76'])).
% 24.51/24.70  thf('78', plain,
% 24.51/24.70      (![X0 : $i]:
% 24.51/24.70         ((r1_tarski @ (k2_relat_1 @ sk_C_8) @ X0)
% 24.51/24.70          | ((sk_C @ X0 @ (k2_relat_1 @ sk_C_8)) = (sk_B_2)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['68', '77'])).
% 24.51/24.70  thf('79', plain,
% 24.51/24.70      (![X8 : $i, X10 : $i]:
% 24.51/24.70         ((r1_tarski @ X8 @ X10) | ~ (r2_hidden @ (sk_C @ X10 @ X8) @ X10))),
% 24.51/24.70      inference('cnf', [status(esa)], [d3_tarski])).
% 24.51/24.70  thf('80', plain,
% 24.51/24.70      (![X0 : $i]:
% 24.51/24.70         (~ (r2_hidden @ sk_B_2 @ X0)
% 24.51/24.70          | (r1_tarski @ (k2_relat_1 @ sk_C_8) @ X0)
% 24.51/24.70          | (r1_tarski @ (k2_relat_1 @ sk_C_8) @ X0))),
% 24.51/24.70      inference('sup-', [status(thm)], ['78', '79'])).
% 24.51/24.70  thf('81', plain,
% 24.51/24.70      (![X0 : $i]:
% 24.51/24.70         ((r1_tarski @ (k2_relat_1 @ sk_C_8) @ X0)
% 24.51/24.70          | ~ (r2_hidden @ sk_B_2 @ X0))),
% 24.51/24.70      inference('simplify', [status(thm)], ['80'])).
% 24.51/24.70  thf('82', plain,
% 24.51/24.70      ((r1_tarski @ (k2_relat_1 @ sk_C_8) @ (k1_tarski @ sk_B_2))),
% 24.51/24.70      inference('sup-', [status(thm)], ['64', '81'])).
% 24.51/24.70  thf('83', plain, (((k2_relat_1 @ sk_C_8) = (k1_tarski @ sk_B_2))),
% 24.51/24.70      inference('demod', [status(thm)], ['63', '82'])).
% 24.51/24.70  thf('84', plain,
% 24.51/24.70      ((((k1_relat_1 @ sk_C_8) != (k1_tarski @ sk_A))
% 24.51/24.70        | ((k2_relat_1 @ sk_C_8) != (k1_tarski @ sk_B_2)))),
% 24.51/24.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.70  thf('85', plain,
% 24.51/24.70      ((((k2_relat_1 @ sk_C_8) != (k1_tarski @ sk_B_2)))
% 24.51/24.70         <= (~ (((k2_relat_1 @ sk_C_8) = (k1_tarski @ sk_B_2))))),
% 24.51/24.70      inference('split', [status(esa)], ['84'])).
% 24.51/24.70  thf('86', plain, ((r2_hidden @ (sk_B @ sk_C_8) @ sk_C_8)),
% 24.51/24.70      inference('demod', [status(thm)], ['19', '28'])).
% 24.51/24.70  thf('87', plain, (((sk_B @ sk_C_8) = (k4_tarski @ sk_A @ sk_B_2))),
% 24.51/24.70      inference('demod', [status(thm)], ['51', '52'])).
% 24.51/24.70  thf(d4_relat_1, axiom,
% 24.51/24.70    (![A:$i,B:$i]:
% 24.51/24.70     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 24.51/24.70       ( ![C:$i]:
% 24.51/24.70         ( ( r2_hidden @ C @ B ) <=>
% 24.51/24.70           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 24.51/24.70  thf('88', plain,
% 24.51/24.70      (![X106 : $i, X107 : $i, X108 : $i, X109 : $i]:
% 24.51/24.70         (~ (r2_hidden @ (k4_tarski @ X106 @ X107) @ X108)
% 24.51/24.70          | (r2_hidden @ X106 @ X109)
% 24.51/24.70          | ((X109) != (k1_relat_1 @ X108)))),
% 24.51/24.70      inference('cnf', [status(esa)], [d4_relat_1])).
% 24.51/24.70  thf('89', plain,
% 24.51/24.70      (![X106 : $i, X107 : $i, X108 : $i]:
% 24.51/24.70         ((r2_hidden @ X106 @ (k1_relat_1 @ X108))
% 24.51/24.70          | ~ (r2_hidden @ (k4_tarski @ X106 @ X107) @ X108))),
% 24.51/24.70      inference('simplify', [status(thm)], ['88'])).
% 24.51/24.70  thf('90', plain,
% 24.51/24.70      (![X0 : $i]:
% 24.51/24.70         (~ (r2_hidden @ (sk_B @ sk_C_8) @ X0)
% 24.51/24.70          | (r2_hidden @ sk_A @ (k1_relat_1 @ X0)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['87', '89'])).
% 24.51/24.70  thf('91', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_8))),
% 24.51/24.70      inference('sup-', [status(thm)], ['86', '90'])).
% 24.51/24.70  thf('92', plain,
% 24.51/24.70      (![X92 : $i, X94 : $i]:
% 24.51/24.70         ((r1_tarski @ (k1_tarski @ X92) @ X94) | ~ (r2_hidden @ X92 @ X94))),
% 24.51/24.70      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 24.51/24.70  thf('93', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_C_8))),
% 24.51/24.70      inference('sup-', [status(thm)], ['91', '92'])).
% 24.51/24.70  thf('94', plain,
% 24.51/24.70      (![X24 : $i, X26 : $i]:
% 24.51/24.70         (((X24) = (X26))
% 24.51/24.70          | ~ (r1_tarski @ X26 @ X24)
% 24.51/24.70          | ~ (r1_tarski @ X24 @ X26))),
% 24.51/24.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.51/24.70  thf('95', plain,
% 24.51/24.70      ((~ (r1_tarski @ (k1_relat_1 @ sk_C_8) @ (k1_tarski @ sk_A))
% 24.51/24.70        | ((k1_relat_1 @ sk_C_8) = (k1_tarski @ sk_A)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['93', '94'])).
% 24.51/24.70  thf('96', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 24.51/24.70      inference('sup-', [status(thm)], ['2', '3'])).
% 24.51/24.70  thf('97', plain,
% 24.51/24.70      (![X8 : $i, X10 : $i]:
% 24.51/24.70         ((r1_tarski @ X8 @ X10) | (r2_hidden @ (sk_C @ X10 @ X8) @ X8))),
% 24.51/24.70      inference('cnf', [status(esa)], [d3_tarski])).
% 24.51/24.70  thf('98', plain,
% 24.51/24.70      (![X108 : $i, X109 : $i, X110 : $i]:
% 24.51/24.70         (~ (r2_hidden @ X110 @ X109)
% 24.51/24.70          | (r2_hidden @ (k4_tarski @ X110 @ (sk_D_2 @ X110 @ X108)) @ X108)
% 24.51/24.70          | ((X109) != (k1_relat_1 @ X108)))),
% 24.51/24.70      inference('cnf', [status(esa)], [d4_relat_1])).
% 24.51/24.70  thf('99', plain,
% 24.51/24.70      (![X108 : $i, X110 : $i]:
% 24.51/24.70         ((r2_hidden @ (k4_tarski @ X110 @ (sk_D_2 @ X110 @ X108)) @ X108)
% 24.51/24.70          | ~ (r2_hidden @ X110 @ (k1_relat_1 @ X108)))),
% 24.51/24.70      inference('simplify', [status(thm)], ['98'])).
% 24.51/24.70  thf('100', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 24.51/24.70          | (r2_hidden @ 
% 24.51/24.70             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 24.51/24.70              (sk_D_2 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 24.51/24.70             X0))),
% 24.51/24.70      inference('sup-', [status(thm)], ['97', '99'])).
% 24.51/24.70  thf('101', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_8))),
% 24.51/24.70      inference('sup-', [status(thm)], ['86', '90'])).
% 24.51/24.70  thf('102', plain,
% 24.51/24.70      (![X108 : $i, X110 : $i]:
% 24.51/24.70         ((r2_hidden @ (k4_tarski @ X110 @ (sk_D_2 @ X110 @ X108)) @ X108)
% 24.51/24.70          | ~ (r2_hidden @ X110 @ (k1_relat_1 @ X108)))),
% 24.51/24.70      inference('simplify', [status(thm)], ['98'])).
% 24.51/24.70  thf('103', plain,
% 24.51/24.70      ((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_C_8)) @ sk_C_8)),
% 24.51/24.70      inference('sup-', [status(thm)], ['101', '102'])).
% 24.51/24.70  thf('104', plain, (((sk_C_8) = (k1_tarski @ (sk_B @ sk_C_8)))),
% 24.51/24.70      inference('demod', [status(thm)], ['30', '31'])).
% 24.51/24.70  thf('105', plain,
% 24.51/24.70      (![X56 : $i, X59 : $i]:
% 24.51/24.70         (((X59) = (X56)) | ~ (r2_hidden @ X59 @ (k1_tarski @ X56)))),
% 24.51/24.70      inference('simplify', [status(thm)], ['8'])).
% 24.51/24.70  thf('106', plain,
% 24.51/24.70      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_8) | ((X0) = (sk_B @ sk_C_8)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['104', '105'])).
% 24.51/24.70  thf('107', plain,
% 24.51/24.70      (((k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_C_8)) = (sk_B @ sk_C_8))),
% 24.51/24.70      inference('sup-', [status(thm)], ['103', '106'])).
% 24.51/24.70  thf('108', plain, ((('#_fresh_sk1' @ sk_C_8) = (sk_B @ sk_C_8))),
% 24.51/24.70      inference('sup+', [status(thm)], ['32', '48'])).
% 24.51/24.70  thf('109', plain,
% 24.51/24.70      (((k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_C_8))
% 24.51/24.70         = ('#_fresh_sk1' @ sk_C_8))),
% 24.51/24.70      inference('demod', [status(thm)], ['107', '108'])).
% 24.51/24.70  thf('110', plain,
% 24.51/24.70      (![X85 : $i, X86 : $i, X87 : $i, X88 : $i]:
% 24.51/24.70         (((X86) = (X85))
% 24.51/24.70          | ~ (r2_hidden @ (k4_tarski @ X86 @ X87) @ 
% 24.51/24.70               (k2_zfmisc_1 @ (k1_tarski @ X85) @ (k1_tarski @ X88))))),
% 24.51/24.70      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 24.51/24.70  thf('111', plain,
% 24.51/24.70      (![X90 : $i, X91 : $i]:
% 24.51/24.70         ((k2_zfmisc_1 @ (k1_tarski @ X90) @ (k1_tarski @ X91))
% 24.51/24.70           = (k1_tarski @ (k4_tarski @ X90 @ X91)))),
% 24.51/24.70      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 24.51/24.70  thf('112', plain,
% 24.51/24.70      (![X85 : $i, X86 : $i, X87 : $i, X88 : $i]:
% 24.51/24.70         (((X86) = (X85))
% 24.51/24.70          | ~ (r2_hidden @ (k4_tarski @ X86 @ X87) @ 
% 24.51/24.70               (k1_tarski @ (k4_tarski @ X85 @ X88))))),
% 24.51/24.70      inference('demod', [status(thm)], ['110', '111'])).
% 24.51/24.70  thf('113', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ 
% 24.51/24.70             (k1_tarski @ ('#_fresh_sk1' @ sk_C_8)))
% 24.51/24.70          | ((X1) = (sk_A)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['109', '112'])).
% 24.51/24.70  thf('114', plain, (((sk_C_8) = (k1_tarski @ ('#_fresh_sk1' @ sk_C_8)))),
% 24.51/24.70      inference('demod', [status(thm)], ['74', '75'])).
% 24.51/24.70  thf('115', plain,
% 24.51/24.70      (![X0 : $i, X1 : $i]:
% 24.51/24.70         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_8) | ((X1) = (sk_A)))),
% 24.51/24.70      inference('demod', [status(thm)], ['113', '114'])).
% 24.51/24.70  thf('116', plain,
% 24.51/24.70      (![X0 : $i]:
% 24.51/24.70         ((r1_tarski @ (k1_relat_1 @ sk_C_8) @ X0)
% 24.51/24.70          | ((sk_C @ X0 @ (k1_relat_1 @ sk_C_8)) = (sk_A)))),
% 24.51/24.70      inference('sup-', [status(thm)], ['100', '115'])).
% 24.51/24.70  thf('117', plain,
% 24.51/24.70      (![X8 : $i, X10 : $i]:
% 24.51/24.70         ((r1_tarski @ X8 @ X10) | ~ (r2_hidden @ (sk_C @ X10 @ X8) @ X10))),
% 24.51/24.70      inference('cnf', [status(esa)], [d3_tarski])).
% 24.51/24.70  thf('118', plain,
% 24.51/24.70      (![X0 : $i]:
% 24.51/24.70         (~ (r2_hidden @ sk_A @ X0)
% 24.51/24.70          | (r1_tarski @ (k1_relat_1 @ sk_C_8) @ X0)
% 24.51/24.70          | (r1_tarski @ (k1_relat_1 @ sk_C_8) @ X0))),
% 24.51/24.70      inference('sup-', [status(thm)], ['116', '117'])).
% 24.51/24.70  thf('119', plain,
% 24.51/24.70      (![X0 : $i]:
% 24.51/24.70         ((r1_tarski @ (k1_relat_1 @ sk_C_8) @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 24.51/24.70      inference('simplify', [status(thm)], ['118'])).
% 24.51/24.70  thf('120', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_8) @ (k1_tarski @ sk_A))),
% 24.51/24.70      inference('sup-', [status(thm)], ['96', '119'])).
% 24.51/24.70  thf('121', plain, (((k1_relat_1 @ sk_C_8) = (k1_tarski @ sk_A))),
% 24.51/24.70      inference('demod', [status(thm)], ['95', '120'])).
% 24.51/24.70  thf('122', plain,
% 24.51/24.70      ((((k1_relat_1 @ sk_C_8) != (k1_tarski @ sk_A)))
% 24.51/24.70         <= (~ (((k1_relat_1 @ sk_C_8) = (k1_tarski @ sk_A))))),
% 24.51/24.70      inference('split', [status(esa)], ['84'])).
% 24.51/24.70  thf('123', plain,
% 24.51/24.70      ((((k1_relat_1 @ sk_C_8) != (k1_relat_1 @ sk_C_8)))
% 24.51/24.70         <= (~ (((k1_relat_1 @ sk_C_8) = (k1_tarski @ sk_A))))),
% 24.51/24.70      inference('sup-', [status(thm)], ['121', '122'])).
% 24.51/24.70  thf('124', plain, ((((k1_relat_1 @ sk_C_8) = (k1_tarski @ sk_A)))),
% 24.51/24.70      inference('simplify', [status(thm)], ['123'])).
% 24.51/24.70  thf('125', plain,
% 24.51/24.70      (~ (((k2_relat_1 @ sk_C_8) = (k1_tarski @ sk_B_2))) | 
% 24.51/24.70       ~ (((k1_relat_1 @ sk_C_8) = (k1_tarski @ sk_A)))),
% 24.51/24.70      inference('split', [status(esa)], ['84'])).
% 24.51/24.70  thf('126', plain, (~ (((k2_relat_1 @ sk_C_8) = (k1_tarski @ sk_B_2)))),
% 24.51/24.70      inference('sat_resolution*', [status(thm)], ['124', '125'])).
% 24.51/24.70  thf('127', plain, (((k2_relat_1 @ sk_C_8) != (k1_tarski @ sk_B_2))),
% 24.51/24.70      inference('simpl_trail', [status(thm)], ['85', '126'])).
% 24.51/24.70  thf('128', plain, ($false),
% 24.51/24.70      inference('simplify_reflect-', [status(thm)], ['83', '127'])).
% 24.51/24.70  
% 24.51/24.70  % SZS output end Refutation
% 24.51/24.70  
% 24.51/24.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
