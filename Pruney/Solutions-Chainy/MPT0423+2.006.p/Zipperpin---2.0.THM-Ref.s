%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.icZZrPLmc6

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:17 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 240 expanded)
%              Number of leaves         :   39 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  833 (1769 expanded)
%              Number of equality atoms :   70 ( 175 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X41: $i] :
      ( ( k1_subset_1 @ X41 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X65: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X65 ) @ ( k1_zfmisc_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X76: $i,X77: $i] :
      ( ( r2_hidden @ X76 @ X77 )
      | ( v1_xboole_0 @ X77 )
      | ~ ( m1_subset_1 @ X76 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X68: $i,X69: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X68 ) @ ( k1_zfmisc_1 @ X69 ) )
      | ~ ( r2_hidden @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('9',plain,(
    ! [X72: $i,X73: $i] :
      ( ( ( k7_setfam_1 @ X73 @ ( k7_setfam_1 @ X73 @ X72 ) )
        = X72 )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X73 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t55_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B
          = ( k1_tarski @ A ) )
       => ( ( k7_setfam_1 @ A @ B )
          = ( k1_tarski @ k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B
            = ( k1_tarski @ A ) )
         => ( ( k7_setfam_1 @ A @ B )
            = ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_setfam_1])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X74 @ X75 ) )
      = ( k3_xboole_0 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_setfam_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf(t51_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('20',plain,(
    ! [X83: $i,X84: $i,X85: $i] :
      ( ~ ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X84 ) ) )
      | ( r1_tarski @ X85 @ X83 )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X84 @ X85 ) @ ( k7_setfam_1 @ X84 @ X83 ) )
      | ~ ( m1_subset_1 @ X85 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X84 ) ) ) ) ),
    inference(cnf,[status(esa)],[t51_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B ) ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) )
    | ( r1_tarski @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ ( k1_tarski @ k1_xboole_0 ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X41: $i] :
      ( ( k1_subset_1 @ X41 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X67: $i] :
      ( ( k2_subset_1 @ X67 )
      = ( k3_subset_1 @ X67 @ ( k1_subset_1 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('25',plain,(
    ! [X42: $i] :
      ( ( k2_subset_1 @ X42 )
      = X42 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('26',plain,(
    ! [X67: $i] :
      ( X67
      = ( k3_subset_1 @ X67 @ ( k1_subset_1 @ X67 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X70: $i,X71: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X70 @ X71 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X70 ) ) )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X70 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('30',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('31',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ X81 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X81 @ X80 ) @ ( k7_setfam_1 @ X81 @ X82 ) )
      | ( r2_hidden @ X80 @ X82 )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X81 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B ) @ X0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('34',plain,(
    ! [X72: $i,X73: $i] :
      ( ( ( k7_setfam_1 @ X73 @ ( k7_setfam_1 @ X73 @ X72 ) )
        = X72 )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X73 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('35',plain,
    ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ ( k1_setfam_1 @ sk_B ) @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ ( k1_setfam_1 @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_setfam_1 @ sk_B ) ) )
    | ( r2_hidden @ k1_xboole_0 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('39',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ ( k1_tarski @ X40 ) )
      | ( X39
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('40',plain,(
    ! [X40: $i] :
      ( r1_tarski @ ( k1_tarski @ X40 ) @ ( k1_tarski @ X40 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('45',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ ( k1_tarski @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k1_setfam_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['12','17'])).

thf('49',plain,(
    r2_hidden @ ( k1_setfam_1 @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('51',plain,(
    r2_hidden @ k1_xboole_0 @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','49','50'])).

thf('52',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('53',plain,(
    r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('55',plain,(
    ! [X70: $i,X71: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X70 @ X71 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X70 ) ) )
      | ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X70 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ ( k1_tarski @ k1_xboole_0 ) ) @ sk_B ),
    inference(demod,[status(thm)],['22','53','56'])).

thf('58',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39
        = ( k1_tarski @ X38 ) )
      | ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ X39 @ ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ ( k1_tarski @ k1_xboole_0 ) )
      = sk_B )
    | ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ ( k1_tarski @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t46_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('65',plain,(
    ! [X78: $i,X79: $i] :
      ( ( ( k7_setfam_1 @ X78 @ X79 )
       != k1_xboole_0 )
      | ( X79 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X78 ) ) ) ) ),
    inference(cnf,[status(esa)],[t46_setfam_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('67',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 != X32 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X32 ) )
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('68',plain,(
    ! [X32: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X32 ) )
     != ( k1_tarski @ X32 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('72',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('73',plain,(
    ! [X32: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X32 ) ) ),
    inference(demod,[status(thm)],['68','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['66','73'])).

thf('75',plain,
    ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ ( k1_tarski @ k1_xboole_0 ) )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['63','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('77',plain,
    ( ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ( k7_setfam_1 @ sk_A @ sk_B )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k1_setfam_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['12','17'])).

thf('80',plain,(
    ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.icZZrPLmc6
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:58:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.05/2.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.05/2.25  % Solved by: fo/fo7.sh
% 2.05/2.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.05/2.25  % done 3212 iterations in 1.794s
% 2.05/2.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.05/2.25  % SZS output start Refutation
% 2.05/2.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.05/2.25  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.05/2.25  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.05/2.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.05/2.25  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 2.05/2.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.05/2.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.05/2.25  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 2.05/2.25  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.05/2.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.05/2.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.05/2.25  thf(sk_A_type, type, sk_A: $i).
% 2.05/2.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.05/2.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.05/2.25  thf(sk_B_type, type, sk_B: $i).
% 2.05/2.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.05/2.25  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.05/2.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.05/2.25  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 2.05/2.25  thf('0', plain, (![X41 : $i]: ((k1_subset_1 @ X41) = (k1_xboole_0))),
% 2.05/2.25      inference('cnf', [status(esa)], [d3_subset_1])).
% 2.05/2.25  thf(dt_k1_subset_1, axiom,
% 2.05/2.25    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.05/2.25  thf('1', plain,
% 2.05/2.25      (![X65 : $i]: (m1_subset_1 @ (k1_subset_1 @ X65) @ (k1_zfmisc_1 @ X65))),
% 2.05/2.25      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 2.05/2.25  thf('2', plain,
% 2.05/2.25      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.05/2.25      inference('sup+', [status(thm)], ['0', '1'])).
% 2.05/2.25  thf(t2_subset, axiom,
% 2.05/2.25    (![A:$i,B:$i]:
% 2.05/2.25     ( ( m1_subset_1 @ A @ B ) =>
% 2.05/2.25       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 2.05/2.25  thf('3', plain,
% 2.05/2.25      (![X76 : $i, X77 : $i]:
% 2.05/2.25         ((r2_hidden @ X76 @ X77)
% 2.05/2.25          | (v1_xboole_0 @ X77)
% 2.05/2.25          | ~ (m1_subset_1 @ X76 @ X77))),
% 2.05/2.26      inference('cnf', [status(esa)], [t2_subset])).
% 2.05/2.26  thf('4', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 2.05/2.26          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['2', '3'])).
% 2.05/2.26  thf(fc1_subset_1, axiom,
% 2.05/2.26    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.05/2.26  thf('5', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 2.05/2.26      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.05/2.26  thf('6', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.05/2.26      inference('clc', [status(thm)], ['4', '5'])).
% 2.05/2.26  thf(t63_subset_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( r2_hidden @ A @ B ) =>
% 2.05/2.26       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.05/2.26  thf('7', plain,
% 2.05/2.26      (![X68 : $i, X69 : $i]:
% 2.05/2.26         ((m1_subset_1 @ (k1_tarski @ X68) @ (k1_zfmisc_1 @ X69))
% 2.05/2.26          | ~ (r2_hidden @ X68 @ X69))),
% 2.05/2.26      inference('cnf', [status(esa)], [t63_subset_1])).
% 2.05/2.26  thf('8', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 2.05/2.26          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['6', '7'])).
% 2.05/2.26  thf(involutiveness_k7_setfam_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.05/2.26       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 2.05/2.26  thf('9', plain,
% 2.05/2.26      (![X72 : $i, X73 : $i]:
% 2.05/2.26         (((k7_setfam_1 @ X73 @ (k7_setfam_1 @ X73 @ X72)) = (X72))
% 2.05/2.26          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X73))))),
% 2.05/2.26      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 2.05/2.26  thf('10', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)))
% 2.05/2.26           = (k1_tarski @ k1_xboole_0))),
% 2.05/2.26      inference('sup-', [status(thm)], ['8', '9'])).
% 2.05/2.26  thf(t55_setfam_1, conjecture,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.05/2.26       ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 2.05/2.26         ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 2.05/2.26  thf(zf_stmt_0, negated_conjecture,
% 2.05/2.26    (~( ![A:$i,B:$i]:
% 2.05/2.26        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.05/2.26          ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 2.05/2.26            ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ) )),
% 2.05/2.26    inference('cnf.neg', [status(esa)], [t55_setfam_1])).
% 2.05/2.26  thf('11', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('12', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf(t69_enumset1, axiom,
% 2.05/2.26    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.05/2.26  thf('13', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 2.05/2.26      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.05/2.26  thf(t12_setfam_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.05/2.26  thf('14', plain,
% 2.05/2.26      (![X74 : $i, X75 : $i]:
% 2.05/2.26         ((k1_setfam_1 @ (k2_tarski @ X74 @ X75)) = (k3_xboole_0 @ X74 @ X75))),
% 2.05/2.26      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.05/2.26  thf('15', plain,
% 2.05/2.26      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 2.05/2.26      inference('sup+', [status(thm)], ['13', '14'])).
% 2.05/2.26  thf(idempotence_k3_xboole_0, axiom,
% 2.05/2.26    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 2.05/2.26  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.05/2.26      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.05/2.26  thf('17', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 2.05/2.26      inference('demod', [status(thm)], ['15', '16'])).
% 2.05/2.26  thf('18', plain, (((k1_setfam_1 @ sk_B) = (sk_A))),
% 2.05/2.26      inference('sup+', [status(thm)], ['12', '17'])).
% 2.05/2.26  thf('19', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_B @ 
% 2.05/2.26        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 2.05/2.26      inference('demod', [status(thm)], ['11', '18'])).
% 2.05/2.26  thf(t51_setfam_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.05/2.26       ( ![C:$i]:
% 2.05/2.26         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.05/2.26           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 2.05/2.26             ( r1_tarski @ B @ C ) ) ) ) ))).
% 2.05/2.26  thf('20', plain,
% 2.05/2.26      (![X83 : $i, X84 : $i, X85 : $i]:
% 2.05/2.26         (~ (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X84)))
% 2.05/2.26          | (r1_tarski @ X85 @ X83)
% 2.05/2.26          | ~ (r1_tarski @ (k7_setfam_1 @ X84 @ X85) @ 
% 2.05/2.26               (k7_setfam_1 @ X84 @ X83))
% 2.05/2.26          | ~ (m1_subset_1 @ X85 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X84))))),
% 2.05/2.26      inference('cnf', [status(esa)], [t51_setfam_1])).
% 2.05/2.26  thf('21', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (~ (m1_subset_1 @ X0 @ 
% 2.05/2.26             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))
% 2.05/2.26          | ~ (r1_tarski @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ X0) @ 
% 2.05/2.26               (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))
% 2.05/2.26          | (r1_tarski @ X0 @ sk_B))),
% 2.05/2.26      inference('sup-', [status(thm)], ['19', '20'])).
% 2.05/2.26  thf('22', plain,
% 2.05/2.26      ((~ (r1_tarski @ (k1_tarski @ k1_xboole_0) @ 
% 2.05/2.26           (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))
% 2.05/2.26        | (r1_tarski @ 
% 2.05/2.26           (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0)) @ 
% 2.05/2.26           sk_B)
% 2.05/2.26        | ~ (m1_subset_1 @ 
% 2.05/2.26             (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0)) @ 
% 2.05/2.26             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B)))))),
% 2.05/2.26      inference('sup-', [status(thm)], ['10', '21'])).
% 2.05/2.26  thf('23', plain, (![X41 : $i]: ((k1_subset_1 @ X41) = (k1_xboole_0))),
% 2.05/2.26      inference('cnf', [status(esa)], [d3_subset_1])).
% 2.05/2.26  thf(t22_subset_1, axiom,
% 2.05/2.26    (![A:$i]:
% 2.05/2.26     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 2.05/2.26  thf('24', plain,
% 2.05/2.26      (![X67 : $i]:
% 2.05/2.26         ((k2_subset_1 @ X67) = (k3_subset_1 @ X67 @ (k1_subset_1 @ X67)))),
% 2.05/2.26      inference('cnf', [status(esa)], [t22_subset_1])).
% 2.05/2.26  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.05/2.26  thf('25', plain, (![X42 : $i]: ((k2_subset_1 @ X42) = (X42))),
% 2.05/2.26      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.05/2.26  thf('26', plain,
% 2.05/2.26      (![X67 : $i]: ((X67) = (k3_subset_1 @ X67 @ (k1_subset_1 @ X67)))),
% 2.05/2.26      inference('demod', [status(thm)], ['24', '25'])).
% 2.05/2.26  thf('27', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 2.05/2.26      inference('sup+', [status(thm)], ['23', '26'])).
% 2.05/2.26  thf('28', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_B @ 
% 2.05/2.26        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 2.05/2.26      inference('demod', [status(thm)], ['11', '18'])).
% 2.05/2.26  thf(dt_k7_setfam_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.05/2.26       ( m1_subset_1 @
% 2.05/2.26         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 2.05/2.26  thf('29', plain,
% 2.05/2.26      (![X70 : $i, X71 : $i]:
% 2.05/2.26         ((m1_subset_1 @ (k7_setfam_1 @ X70 @ X71) @ 
% 2.05/2.26           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X70)))
% 2.05/2.26          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X70))))),
% 2.05/2.26      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 2.05/2.26  thf('30', plain,
% 2.05/2.26      ((m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B) @ 
% 2.05/2.26        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 2.05/2.26      inference('sup-', [status(thm)], ['28', '29'])).
% 2.05/2.26  thf(t49_setfam_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.05/2.26       ( ![C:$i]:
% 2.05/2.26         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.05/2.26           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 2.05/2.26             ( r2_hidden @ C @ B ) ) ) ) ))).
% 2.05/2.26  thf('31', plain,
% 2.05/2.26      (![X80 : $i, X81 : $i, X82 : $i]:
% 2.05/2.26         (~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ X81))
% 2.05/2.26          | ~ (r2_hidden @ (k3_subset_1 @ X81 @ X80) @ 
% 2.05/2.26               (k7_setfam_1 @ X81 @ X82))
% 2.05/2.26          | (r2_hidden @ X80 @ X82)
% 2.05/2.26          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X81))))),
% 2.05/2.26      inference('cnf', [status(esa)], [t49_setfam_1])).
% 2.05/2.26  thf('32', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((r2_hidden @ X0 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))
% 2.05/2.26          | ~ (r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B) @ X0) @ 
% 2.05/2.26               (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ 
% 2.05/2.26                (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B)))
% 2.05/2.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 2.05/2.26      inference('sup-', [status(thm)], ['30', '31'])).
% 2.05/2.26  thf('33', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_B @ 
% 2.05/2.26        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 2.05/2.26      inference('demod', [status(thm)], ['11', '18'])).
% 2.05/2.26  thf('34', plain,
% 2.05/2.26      (![X72 : $i, X73 : $i]:
% 2.05/2.26         (((k7_setfam_1 @ X73 @ (k7_setfam_1 @ X73 @ X72)) = (X72))
% 2.05/2.26          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X73))))),
% 2.05/2.26      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 2.05/2.26  thf('35', plain,
% 2.05/2.26      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ 
% 2.05/2.26         (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B)) = (sk_B))),
% 2.05/2.26      inference('sup-', [status(thm)], ['33', '34'])).
% 2.05/2.26  thf('36', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((r2_hidden @ X0 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))
% 2.05/2.26          | ~ (r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B) @ X0) @ sk_B)
% 2.05/2.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 2.05/2.26      inference('demod', [status(thm)], ['32', '35'])).
% 2.05/2.26  thf('37', plain,
% 2.05/2.26      ((~ (r2_hidden @ (k1_setfam_1 @ sk_B) @ sk_B)
% 2.05/2.26        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B)))
% 2.05/2.26        | (r2_hidden @ k1_xboole_0 @ 
% 2.05/2.26           (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['27', '36'])).
% 2.05/2.26  thf('38', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf(t39_zfmisc_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 2.05/2.26       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 2.05/2.26  thf('39', plain,
% 2.05/2.26      (![X39 : $i, X40 : $i]:
% 2.05/2.26         ((r1_tarski @ X39 @ (k1_tarski @ X40)) | ((X39) != (k1_tarski @ X40)))),
% 2.05/2.26      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 2.05/2.26  thf('40', plain,
% 2.05/2.26      (![X40 : $i]: (r1_tarski @ (k1_tarski @ X40) @ (k1_tarski @ X40))),
% 2.05/2.26      inference('simplify', [status(thm)], ['39'])).
% 2.05/2.26  thf('41', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 2.05/2.26      inference('sup+', [status(thm)], ['38', '40'])).
% 2.05/2.26  thf('42', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('43', plain, ((r1_tarski @ sk_B @ sk_B)),
% 2.05/2.26      inference('demod', [status(thm)], ['41', '42'])).
% 2.05/2.26  thf('44', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf(t37_zfmisc_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 2.05/2.26  thf('45', plain,
% 2.05/2.26      (![X35 : $i, X36 : $i]:
% 2.05/2.26         ((r2_hidden @ X35 @ X36) | ~ (r1_tarski @ (k1_tarski @ X35) @ X36))),
% 2.05/2.26      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 2.05/2.26  thf('46', plain,
% 2.05/2.26      (![X0 : $i]: (~ (r1_tarski @ sk_B @ X0) | (r2_hidden @ sk_A @ X0))),
% 2.05/2.26      inference('sup-', [status(thm)], ['44', '45'])).
% 2.05/2.26  thf('47', plain, ((r2_hidden @ sk_A @ sk_B)),
% 2.05/2.26      inference('sup-', [status(thm)], ['43', '46'])).
% 2.05/2.26  thf('48', plain, (((k1_setfam_1 @ sk_B) = (sk_A))),
% 2.05/2.26      inference('sup+', [status(thm)], ['12', '17'])).
% 2.05/2.26  thf('49', plain, ((r2_hidden @ (k1_setfam_1 @ sk_B) @ sk_B)),
% 2.05/2.26      inference('demod', [status(thm)], ['47', '48'])).
% 2.05/2.26  thf('50', plain,
% 2.05/2.26      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.05/2.26      inference('sup+', [status(thm)], ['0', '1'])).
% 2.05/2.26  thf('51', plain,
% 2.05/2.26      ((r2_hidden @ k1_xboole_0 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))),
% 2.05/2.26      inference('demod', [status(thm)], ['37', '49', '50'])).
% 2.05/2.26  thf('52', plain,
% 2.05/2.26      (![X35 : $i, X37 : $i]:
% 2.05/2.26         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 2.05/2.26      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 2.05/2.26  thf('53', plain,
% 2.05/2.26      ((r1_tarski @ (k1_tarski @ k1_xboole_0) @ 
% 2.05/2.26        (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))),
% 2.05/2.26      inference('sup-', [status(thm)], ['51', '52'])).
% 2.05/2.26  thf('54', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 2.05/2.26          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['6', '7'])).
% 2.05/2.26  thf('55', plain,
% 2.05/2.26      (![X70 : $i, X71 : $i]:
% 2.05/2.26         ((m1_subset_1 @ (k7_setfam_1 @ X70 @ X71) @ 
% 2.05/2.26           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X70)))
% 2.05/2.26          | ~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X70))))),
% 2.05/2.26      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 2.05/2.26  thf('56', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (m1_subset_1 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) @ 
% 2.05/2.26          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['54', '55'])).
% 2.05/2.26  thf('57', plain,
% 2.05/2.26      ((r1_tarski @ 
% 2.05/2.26        (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0)) @ sk_B)),
% 2.05/2.26      inference('demod', [status(thm)], ['22', '53', '56'])).
% 2.05/2.26  thf('58', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('59', plain,
% 2.05/2.26      (![X38 : $i, X39 : $i]:
% 2.05/2.26         (((X39) = (k1_tarski @ X38))
% 2.05/2.26          | ((X39) = (k1_xboole_0))
% 2.05/2.26          | ~ (r1_tarski @ X39 @ (k1_tarski @ X38)))),
% 2.05/2.26      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 2.05/2.26  thf('60', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (~ (r1_tarski @ X0 @ sk_B)
% 2.05/2.26          | ((X0) = (k1_xboole_0))
% 2.05/2.26          | ((X0) = (k1_tarski @ sk_A)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['58', '59'])).
% 2.05/2.26  thf('61', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('62', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 2.05/2.26      inference('demod', [status(thm)], ['60', '61'])).
% 2.05/2.26  thf('63', plain,
% 2.05/2.26      ((((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0))
% 2.05/2.26          = (sk_B))
% 2.05/2.26        | ((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0))
% 2.05/2.26            = (k1_xboole_0)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['57', '62'])).
% 2.05/2.26  thf('64', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 2.05/2.26          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['6', '7'])).
% 2.05/2.26  thf(t46_setfam_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.05/2.26       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.05/2.26            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 2.05/2.26  thf('65', plain,
% 2.05/2.26      (![X78 : $i, X79 : $i]:
% 2.05/2.26         (((k7_setfam_1 @ X78 @ X79) != (k1_xboole_0))
% 2.05/2.26          | ((X79) = (k1_xboole_0))
% 2.05/2.26          | ~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X78))))),
% 2.05/2.26      inference('cnf', [status(esa)], [t46_setfam_1])).
% 2.05/2.26  thf('66', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 2.05/2.26          | ((k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['64', '65'])).
% 2.05/2.26  thf(t20_zfmisc_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 2.05/2.26         ( k1_tarski @ A ) ) <=>
% 2.05/2.26       ( ( A ) != ( B ) ) ))).
% 2.05/2.26  thf('67', plain,
% 2.05/2.26      (![X32 : $i, X33 : $i]:
% 2.05/2.26         (((X33) != (X32))
% 2.05/2.26          | ((k4_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X32))
% 2.05/2.26              != (k1_tarski @ X33)))),
% 2.05/2.26      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 2.05/2.26  thf('68', plain,
% 2.05/2.26      (![X32 : $i]:
% 2.05/2.26         ((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X32))
% 2.05/2.26           != (k1_tarski @ X32))),
% 2.05/2.26      inference('simplify', [status(thm)], ['67'])).
% 2.05/2.26  thf('69', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.05/2.26      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.05/2.26  thf(t100_xboole_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.05/2.26  thf('70', plain,
% 2.05/2.26      (![X1 : $i, X2 : $i]:
% 2.05/2.26         ((k4_xboole_0 @ X1 @ X2)
% 2.05/2.26           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.05/2.26      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.05/2.26  thf('71', plain,
% 2.05/2.26      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.05/2.26      inference('sup+', [status(thm)], ['69', '70'])).
% 2.05/2.26  thf(t92_xboole_1, axiom,
% 2.05/2.26    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 2.05/2.26  thf('72', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 2.05/2.26      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.05/2.26  thf('73', plain, (![X32 : $i]: ((k1_xboole_0) != (k1_tarski @ X32))),
% 2.05/2.26      inference('demod', [status(thm)], ['68', '71', '72'])).
% 2.05/2.26  thf('74', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0))),
% 2.05/2.26      inference('clc', [status(thm)], ['66', '73'])).
% 2.05/2.26  thf('75', plain,
% 2.05/2.26      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0))
% 2.05/2.26         = (sk_B))),
% 2.05/2.26      inference('simplify_reflect-', [status(thm)], ['63', '74'])).
% 2.05/2.26  thf('76', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)))
% 2.05/2.26           = (k1_tarski @ k1_xboole_0))),
% 2.05/2.26      inference('sup-', [status(thm)], ['8', '9'])).
% 2.05/2.26  thf('77', plain,
% 2.05/2.26      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B) = (k1_tarski @ k1_xboole_0))),
% 2.05/2.26      inference('sup+', [status(thm)], ['75', '76'])).
% 2.05/2.26  thf('78', plain,
% 2.05/2.26      (((k7_setfam_1 @ sk_A @ sk_B) != (k1_tarski @ k1_xboole_0))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('79', plain, (((k1_setfam_1 @ sk_B) = (sk_A))),
% 2.05/2.26      inference('sup+', [status(thm)], ['12', '17'])).
% 2.05/2.26  thf('80', plain,
% 2.05/2.26      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B)
% 2.05/2.26         != (k1_tarski @ k1_xboole_0))),
% 2.05/2.26      inference('demod', [status(thm)], ['78', '79'])).
% 2.05/2.26  thf('81', plain, ($false),
% 2.05/2.26      inference('simplify_reflect-', [status(thm)], ['77', '80'])).
% 2.05/2.26  
% 2.05/2.26  % SZS output end Refutation
% 2.05/2.26  
% 2.05/2.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
