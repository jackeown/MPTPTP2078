%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tRbTJ1Ll0J

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:16 EST 2020

% Result     : Theorem 28.58s
% Output     : Refutation 28.58s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 240 expanded)
%              Number of leaves         :   39 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  840 (1797 expanded)
%              Number of equality atoms :   70 ( 175 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X44: $i] :
      ( ( k1_subset_1 @ X44 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X68: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X68 ) @ ( k1_zfmisc_1 @ X68 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ X42 )
      | ( r2_hidden @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X69: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X69 ) ) ),
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
    ! [X71: $i,X72: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X71 ) @ ( k1_zfmisc_1 @ X72 ) )
      | ~ ( r2_hidden @ X71 @ X72 ) ) ),
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
    ! [X75: $i,X76: $i] :
      ( ( ( k7_setfam_1 @ X76 @ ( k7_setfam_1 @ X76 @ X75 ) )
        = X75 )
      | ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X76 ) ) ) ) ),
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
    ! [X77: $i,X78: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X77 @ X78 ) )
      = ( k3_xboole_0 @ X77 @ X78 ) ) ),
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
    ! [X84: $i,X85: $i,X86: $i] :
      ( ~ ( m1_subset_1 @ X84 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X85 ) ) )
      | ( r1_tarski @ X86 @ X84 )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X85 @ X86 ) @ ( k7_setfam_1 @ X85 @ X84 ) )
      | ~ ( m1_subset_1 @ X86 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X85 ) ) ) ) ),
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
    ! [X44: $i] :
      ( ( k1_subset_1 @ X44 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X70: $i] :
      ( ( k2_subset_1 @ X70 )
      = ( k3_subset_1 @ X70 @ ( k1_subset_1 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('25',plain,(
    ! [X45: $i] :
      ( ( k2_subset_1 @ X45 )
      = X45 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('26',plain,(
    ! [X70: $i] :
      ( X70
      = ( k3_subset_1 @ X70 @ ( k1_subset_1 @ X70 ) ) ) ),
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
    ! [X73: $i,X74: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X73 @ X74 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X73 ) ) )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X73 ) ) ) ) ),
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
    ! [X81: $i,X82: $i,X83: $i] :
      ( ~ ( m1_subset_1 @ X81 @ ( k1_zfmisc_1 @ X82 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X82 @ X81 ) @ ( k7_setfam_1 @ X82 @ X83 ) )
      | ( r2_hidden @ X81 @ X83 )
      | ~ ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X82 ) ) ) ) ),
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
    ! [X75: $i,X76: $i] :
      ( ( ( k7_setfam_1 @ X76 @ ( k7_setfam_1 @ X76 @ X75 ) )
        = X75 )
      | ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X76 ) ) ) ) ),
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

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('39',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ X36 @ ( k1_tarski @ X37 ) )
      | ( X36
       != ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('40',plain,(
    ! [X37: $i] :
      ( r1_tarski @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X37 ) ) ),
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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('45',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k1_tarski @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

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
    ! [X32: $i,X34: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('53',plain,(
    r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k7_setfam_1 @ ( k1_setfam_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('55',plain,(
    ! [X73: $i,X74: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X73 @ X74 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X73 ) ) )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X73 ) ) ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ( X36
        = ( k1_tarski @ X35 ) )
      | ( X36 = k1_xboole_0 )
      | ~ ( r1_tarski @ X36 @ ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

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
    ! [X79: $i,X80: $i] :
      ( ( ( k7_setfam_1 @ X79 @ X80 )
       != k1_xboole_0 )
      | ( X80 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X79 ) ) ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( X39 != X38 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X38 ) )
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('68',plain,(
    ! [X38: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X38 ) )
     != ( k1_tarski @ X38 ) ) ),
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
    ! [X38: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X38 ) ) ),
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
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tRbTJ1Ll0J
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 28.58/28.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 28.58/28.78  % Solved by: fo/fo7.sh
% 28.58/28.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 28.58/28.78  % done 10880 iterations in 28.354s
% 28.58/28.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 28.58/28.78  % SZS output start Refutation
% 28.58/28.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 28.58/28.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 28.58/28.78  thf(sk_B_type, type, sk_B: $i).
% 28.58/28.78  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 28.58/28.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 28.58/28.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 28.58/28.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 28.58/28.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 28.58/28.78  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 28.58/28.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 28.58/28.78  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 28.58/28.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 28.58/28.78  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 28.58/28.78  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 28.58/28.78  thf(sk_A_type, type, sk_A: $i).
% 28.58/28.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 28.58/28.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 28.58/28.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 28.58/28.78  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 28.58/28.78  thf('0', plain, (![X44 : $i]: ((k1_subset_1 @ X44) = (k1_xboole_0))),
% 28.58/28.78      inference('cnf', [status(esa)], [d3_subset_1])).
% 28.58/28.78  thf(dt_k1_subset_1, axiom,
% 28.58/28.78    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 28.58/28.78  thf('1', plain,
% 28.58/28.78      (![X68 : $i]: (m1_subset_1 @ (k1_subset_1 @ X68) @ (k1_zfmisc_1 @ X68))),
% 28.58/28.78      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 28.58/28.78  thf('2', plain,
% 28.58/28.78      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 28.58/28.78      inference('sup+', [status(thm)], ['0', '1'])).
% 28.58/28.78  thf(d2_subset_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( ( v1_xboole_0 @ A ) =>
% 28.58/28.78         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 28.58/28.78       ( ( ~( v1_xboole_0 @ A ) ) =>
% 28.58/28.78         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 28.58/28.78  thf('3', plain,
% 28.58/28.78      (![X41 : $i, X42 : $i]:
% 28.58/28.78         (~ (m1_subset_1 @ X41 @ X42)
% 28.58/28.78          | (r2_hidden @ X41 @ X42)
% 28.58/28.78          | (v1_xboole_0 @ X42))),
% 28.58/28.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 28.58/28.78  thf('4', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 28.58/28.78          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 28.58/28.78      inference('sup-', [status(thm)], ['2', '3'])).
% 28.58/28.78  thf(fc1_subset_1, axiom,
% 28.58/28.78    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 28.58/28.78  thf('5', plain, (![X69 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X69))),
% 28.58/28.78      inference('cnf', [status(esa)], [fc1_subset_1])).
% 28.58/28.78  thf('6', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 28.58/28.78      inference('clc', [status(thm)], ['4', '5'])).
% 28.58/28.78  thf(t63_subset_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( r2_hidden @ A @ B ) =>
% 28.58/28.78       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 28.58/28.78  thf('7', plain,
% 28.58/28.78      (![X71 : $i, X72 : $i]:
% 28.58/28.78         ((m1_subset_1 @ (k1_tarski @ X71) @ (k1_zfmisc_1 @ X72))
% 28.58/28.78          | ~ (r2_hidden @ X71 @ X72))),
% 28.58/28.78      inference('cnf', [status(esa)], [t63_subset_1])).
% 28.58/28.78  thf('8', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 28.58/28.78          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 28.58/28.78      inference('sup-', [status(thm)], ['6', '7'])).
% 28.58/28.78  thf(involutiveness_k7_setfam_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.58/28.78       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 28.58/28.78  thf('9', plain,
% 28.58/28.78      (![X75 : $i, X76 : $i]:
% 28.58/28.78         (((k7_setfam_1 @ X76 @ (k7_setfam_1 @ X76 @ X75)) = (X75))
% 28.58/28.78          | ~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X76))))),
% 28.58/28.78      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 28.58/28.78  thf('10', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)))
% 28.58/28.78           = (k1_tarski @ k1_xboole_0))),
% 28.58/28.78      inference('sup-', [status(thm)], ['8', '9'])).
% 28.58/28.78  thf(t55_setfam_1, conjecture,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.58/28.78       ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 28.58/28.78         ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 28.58/28.78  thf(zf_stmt_0, negated_conjecture,
% 28.58/28.78    (~( ![A:$i,B:$i]:
% 28.58/28.78        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.58/28.78          ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 28.58/28.78            ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ) )),
% 28.58/28.78    inference('cnf.neg', [status(esa)], [t55_setfam_1])).
% 28.58/28.78  thf('11', plain,
% 28.58/28.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 28.58/28.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.58/28.78  thf('12', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 28.58/28.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.58/28.78  thf(t69_enumset1, axiom,
% 28.58/28.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 28.58/28.78  thf('13', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 28.58/28.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 28.58/28.78  thf(t12_setfam_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 28.58/28.78  thf('14', plain,
% 28.58/28.78      (![X77 : $i, X78 : $i]:
% 28.58/28.78         ((k1_setfam_1 @ (k2_tarski @ X77 @ X78)) = (k3_xboole_0 @ X77 @ X78))),
% 28.58/28.78      inference('cnf', [status(esa)], [t12_setfam_1])).
% 28.58/28.78  thf('15', plain,
% 28.58/28.78      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 28.58/28.78      inference('sup+', [status(thm)], ['13', '14'])).
% 28.58/28.78  thf(idempotence_k3_xboole_0, axiom,
% 28.58/28.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 28.58/28.78  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 28.58/28.78      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 28.58/28.78  thf('17', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 28.58/28.78      inference('demod', [status(thm)], ['15', '16'])).
% 28.58/28.78  thf('18', plain, (((k1_setfam_1 @ sk_B) = (sk_A))),
% 28.58/28.78      inference('sup+', [status(thm)], ['12', '17'])).
% 28.58/28.78  thf('19', plain,
% 28.58/28.78      ((m1_subset_1 @ sk_B @ 
% 28.58/28.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 28.58/28.78      inference('demod', [status(thm)], ['11', '18'])).
% 28.58/28.78  thf(t51_setfam_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.58/28.78       ( ![C:$i]:
% 28.58/28.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.58/28.78           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 28.58/28.78             ( r1_tarski @ B @ C ) ) ) ) ))).
% 28.58/28.78  thf('20', plain,
% 28.58/28.78      (![X84 : $i, X85 : $i, X86 : $i]:
% 28.58/28.78         (~ (m1_subset_1 @ X84 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X85)))
% 28.58/28.78          | (r1_tarski @ X86 @ X84)
% 28.58/28.78          | ~ (r1_tarski @ (k7_setfam_1 @ X85 @ X86) @ 
% 28.58/28.78               (k7_setfam_1 @ X85 @ X84))
% 28.58/28.78          | ~ (m1_subset_1 @ X86 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X85))))),
% 28.58/28.78      inference('cnf', [status(esa)], [t51_setfam_1])).
% 28.58/28.78  thf('21', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         (~ (m1_subset_1 @ X0 @ 
% 28.58/28.78             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))
% 28.58/28.78          | ~ (r1_tarski @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ X0) @ 
% 28.58/28.78               (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))
% 28.58/28.78          | (r1_tarski @ X0 @ sk_B))),
% 28.58/28.78      inference('sup-', [status(thm)], ['19', '20'])).
% 28.58/28.78  thf('22', plain,
% 28.58/28.78      ((~ (r1_tarski @ (k1_tarski @ k1_xboole_0) @ 
% 28.58/28.78           (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))
% 28.58/28.78        | (r1_tarski @ 
% 28.58/28.78           (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0)) @ 
% 28.58/28.78           sk_B)
% 28.58/28.78        | ~ (m1_subset_1 @ 
% 28.58/28.78             (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0)) @ 
% 28.58/28.78             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B)))))),
% 28.58/28.78      inference('sup-', [status(thm)], ['10', '21'])).
% 28.58/28.78  thf('23', plain, (![X44 : $i]: ((k1_subset_1 @ X44) = (k1_xboole_0))),
% 28.58/28.78      inference('cnf', [status(esa)], [d3_subset_1])).
% 28.58/28.78  thf(t22_subset_1, axiom,
% 28.58/28.78    (![A:$i]:
% 28.58/28.78     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 28.58/28.78  thf('24', plain,
% 28.58/28.78      (![X70 : $i]:
% 28.58/28.78         ((k2_subset_1 @ X70) = (k3_subset_1 @ X70 @ (k1_subset_1 @ X70)))),
% 28.58/28.78      inference('cnf', [status(esa)], [t22_subset_1])).
% 28.58/28.78  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 28.58/28.78  thf('25', plain, (![X45 : $i]: ((k2_subset_1 @ X45) = (X45))),
% 28.58/28.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 28.58/28.78  thf('26', plain,
% 28.58/28.78      (![X70 : $i]: ((X70) = (k3_subset_1 @ X70 @ (k1_subset_1 @ X70)))),
% 28.58/28.78      inference('demod', [status(thm)], ['24', '25'])).
% 28.58/28.78  thf('27', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 28.58/28.78      inference('sup+', [status(thm)], ['23', '26'])).
% 28.58/28.78  thf('28', plain,
% 28.58/28.78      ((m1_subset_1 @ sk_B @ 
% 28.58/28.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 28.58/28.78      inference('demod', [status(thm)], ['11', '18'])).
% 28.58/28.78  thf(dt_k7_setfam_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.58/28.78       ( m1_subset_1 @
% 28.58/28.78         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 28.58/28.78  thf('29', plain,
% 28.58/28.78      (![X73 : $i, X74 : $i]:
% 28.58/28.78         ((m1_subset_1 @ (k7_setfam_1 @ X73 @ X74) @ 
% 28.58/28.78           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X73)))
% 28.58/28.78          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X73))))),
% 28.58/28.78      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 28.58/28.78  thf('30', plain,
% 28.58/28.78      ((m1_subset_1 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B) @ 
% 28.58/28.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 28.58/28.78      inference('sup-', [status(thm)], ['28', '29'])).
% 28.58/28.78  thf(t49_setfam_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.58/28.78       ( ![C:$i]:
% 28.58/28.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 28.58/28.78           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 28.58/28.78             ( r2_hidden @ C @ B ) ) ) ) ))).
% 28.58/28.78  thf('31', plain,
% 28.58/28.78      (![X81 : $i, X82 : $i, X83 : $i]:
% 28.58/28.78         (~ (m1_subset_1 @ X81 @ (k1_zfmisc_1 @ X82))
% 28.58/28.78          | ~ (r2_hidden @ (k3_subset_1 @ X82 @ X81) @ 
% 28.58/28.78               (k7_setfam_1 @ X82 @ X83))
% 28.58/28.78          | (r2_hidden @ X81 @ X83)
% 28.58/28.78          | ~ (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X82))))),
% 28.58/28.78      inference('cnf', [status(esa)], [t49_setfam_1])).
% 28.58/28.78  thf('32', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         ((r2_hidden @ X0 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))
% 28.58/28.78          | ~ (r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B) @ X0) @ 
% 28.58/28.78               (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ 
% 28.58/28.78                (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B)))
% 28.58/28.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 28.58/28.78      inference('sup-', [status(thm)], ['30', '31'])).
% 28.58/28.78  thf('33', plain,
% 28.58/28.78      ((m1_subset_1 @ sk_B @ 
% 28.58/28.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 28.58/28.78      inference('demod', [status(thm)], ['11', '18'])).
% 28.58/28.78  thf('34', plain,
% 28.58/28.78      (![X75 : $i, X76 : $i]:
% 28.58/28.78         (((k7_setfam_1 @ X76 @ (k7_setfam_1 @ X76 @ X75)) = (X75))
% 28.58/28.78          | ~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X76))))),
% 28.58/28.78      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 28.58/28.78  thf('35', plain,
% 28.58/28.78      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ 
% 28.58/28.78         (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B)) = (sk_B))),
% 28.58/28.78      inference('sup-', [status(thm)], ['33', '34'])).
% 28.58/28.78  thf('36', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         ((r2_hidden @ X0 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))
% 28.58/28.78          | ~ (r2_hidden @ (k3_subset_1 @ (k1_setfam_1 @ sk_B) @ X0) @ sk_B)
% 28.58/28.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B))))),
% 28.58/28.78      inference('demod', [status(thm)], ['32', '35'])).
% 28.58/28.78  thf('37', plain,
% 28.58/28.78      ((~ (r2_hidden @ (k1_setfam_1 @ sk_B) @ sk_B)
% 28.58/28.78        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_setfam_1 @ sk_B)))
% 28.58/28.78        | (r2_hidden @ k1_xboole_0 @ 
% 28.58/28.78           (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B)))),
% 28.58/28.78      inference('sup-', [status(thm)], ['27', '36'])).
% 28.58/28.78  thf('38', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 28.58/28.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.58/28.78  thf(l3_zfmisc_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 28.58/28.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 28.58/28.78  thf('39', plain,
% 28.58/28.78      (![X36 : $i, X37 : $i]:
% 28.58/28.78         ((r1_tarski @ X36 @ (k1_tarski @ X37)) | ((X36) != (k1_tarski @ X37)))),
% 28.58/28.78      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 28.58/28.78  thf('40', plain,
% 28.58/28.78      (![X37 : $i]: (r1_tarski @ (k1_tarski @ X37) @ (k1_tarski @ X37))),
% 28.58/28.78      inference('simplify', [status(thm)], ['39'])).
% 28.58/28.78  thf('41', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 28.58/28.78      inference('sup+', [status(thm)], ['38', '40'])).
% 28.58/28.78  thf('42', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 28.58/28.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.58/28.78  thf('43', plain, ((r1_tarski @ sk_B @ sk_B)),
% 28.58/28.78      inference('demod', [status(thm)], ['41', '42'])).
% 28.58/28.78  thf('44', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 28.58/28.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.58/28.78  thf(l1_zfmisc_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 28.58/28.78  thf('45', plain,
% 28.58/28.78      (![X32 : $i, X33 : $i]:
% 28.58/28.78         ((r2_hidden @ X32 @ X33) | ~ (r1_tarski @ (k1_tarski @ X32) @ X33))),
% 28.58/28.78      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 28.58/28.78  thf('46', plain,
% 28.58/28.78      (![X0 : $i]: (~ (r1_tarski @ sk_B @ X0) | (r2_hidden @ sk_A @ X0))),
% 28.58/28.78      inference('sup-', [status(thm)], ['44', '45'])).
% 28.58/28.78  thf('47', plain, ((r2_hidden @ sk_A @ sk_B)),
% 28.58/28.78      inference('sup-', [status(thm)], ['43', '46'])).
% 28.58/28.78  thf('48', plain, (((k1_setfam_1 @ sk_B) = (sk_A))),
% 28.58/28.78      inference('sup+', [status(thm)], ['12', '17'])).
% 28.58/28.78  thf('49', plain, ((r2_hidden @ (k1_setfam_1 @ sk_B) @ sk_B)),
% 28.58/28.78      inference('demod', [status(thm)], ['47', '48'])).
% 28.58/28.78  thf('50', plain,
% 28.58/28.78      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 28.58/28.78      inference('sup+', [status(thm)], ['0', '1'])).
% 28.58/28.78  thf('51', plain,
% 28.58/28.78      ((r2_hidden @ k1_xboole_0 @ (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))),
% 28.58/28.78      inference('demod', [status(thm)], ['37', '49', '50'])).
% 28.58/28.78  thf('52', plain,
% 28.58/28.78      (![X32 : $i, X34 : $i]:
% 28.58/28.78         ((r1_tarski @ (k1_tarski @ X32) @ X34) | ~ (r2_hidden @ X32 @ X34))),
% 28.58/28.78      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 28.58/28.78  thf('53', plain,
% 28.58/28.78      ((r1_tarski @ (k1_tarski @ k1_xboole_0) @ 
% 28.58/28.78        (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B))),
% 28.58/28.78      inference('sup-', [status(thm)], ['51', '52'])).
% 28.58/28.78  thf('54', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 28.58/28.78          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 28.58/28.78      inference('sup-', [status(thm)], ['6', '7'])).
% 28.58/28.78  thf('55', plain,
% 28.58/28.78      (![X73 : $i, X74 : $i]:
% 28.58/28.78         ((m1_subset_1 @ (k7_setfam_1 @ X73 @ X74) @ 
% 28.58/28.78           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X73)))
% 28.58/28.78          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X73))))),
% 28.58/28.78      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 28.58/28.78  thf('56', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         (m1_subset_1 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) @ 
% 28.58/28.78          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 28.58/28.78      inference('sup-', [status(thm)], ['54', '55'])).
% 28.58/28.78  thf('57', plain,
% 28.58/28.78      ((r1_tarski @ 
% 28.58/28.78        (k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0)) @ sk_B)),
% 28.58/28.78      inference('demod', [status(thm)], ['22', '53', '56'])).
% 28.58/28.78  thf('58', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 28.58/28.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.58/28.78  thf('59', plain,
% 28.58/28.78      (![X35 : $i, X36 : $i]:
% 28.58/28.78         (((X36) = (k1_tarski @ X35))
% 28.58/28.78          | ((X36) = (k1_xboole_0))
% 28.58/28.78          | ~ (r1_tarski @ X36 @ (k1_tarski @ X35)))),
% 28.58/28.78      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 28.58/28.78  thf('60', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         (~ (r1_tarski @ X0 @ sk_B)
% 28.58/28.78          | ((X0) = (k1_xboole_0))
% 28.58/28.78          | ((X0) = (k1_tarski @ sk_A)))),
% 28.58/28.78      inference('sup-', [status(thm)], ['58', '59'])).
% 28.58/28.78  thf('61', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 28.58/28.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.58/28.78  thf('62', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 28.58/28.78      inference('demod', [status(thm)], ['60', '61'])).
% 28.58/28.78  thf('63', plain,
% 28.58/28.78      ((((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0))
% 28.58/28.78          = (sk_B))
% 28.58/28.78        | ((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0))
% 28.58/28.78            = (k1_xboole_0)))),
% 28.58/28.78      inference('sup-', [status(thm)], ['57', '62'])).
% 28.58/28.78  thf('64', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 28.58/28.78          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 28.58/28.78      inference('sup-', [status(thm)], ['6', '7'])).
% 28.58/28.78  thf(t46_setfam_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.58/28.78       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 28.58/28.78            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 28.58/28.78  thf('65', plain,
% 28.58/28.78      (![X79 : $i, X80 : $i]:
% 28.58/28.78         (((k7_setfam_1 @ X79 @ X80) != (k1_xboole_0))
% 28.58/28.78          | ((X80) = (k1_xboole_0))
% 28.58/28.78          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X79))))),
% 28.58/28.78      inference('cnf', [status(esa)], [t46_setfam_1])).
% 28.58/28.78  thf('66', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 28.58/28.78          | ((k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0)))),
% 28.58/28.78      inference('sup-', [status(thm)], ['64', '65'])).
% 28.58/28.78  thf(t20_zfmisc_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 28.58/28.78         ( k1_tarski @ A ) ) <=>
% 28.58/28.78       ( ( A ) != ( B ) ) ))).
% 28.58/28.78  thf('67', plain,
% 28.58/28.78      (![X38 : $i, X39 : $i]:
% 28.58/28.78         (((X39) != (X38))
% 28.58/28.78          | ((k4_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X38))
% 28.58/28.78              != (k1_tarski @ X39)))),
% 28.58/28.78      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 28.58/28.78  thf('68', plain,
% 28.58/28.78      (![X38 : $i]:
% 28.58/28.78         ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X38))
% 28.58/28.78           != (k1_tarski @ X38))),
% 28.58/28.78      inference('simplify', [status(thm)], ['67'])).
% 28.58/28.78  thf('69', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 28.58/28.78      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 28.58/28.78  thf(t100_xboole_1, axiom,
% 28.58/28.78    (![A:$i,B:$i]:
% 28.58/28.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 28.58/28.78  thf('70', plain,
% 28.58/28.78      (![X1 : $i, X2 : $i]:
% 28.58/28.78         ((k4_xboole_0 @ X1 @ X2)
% 28.58/28.78           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 28.58/28.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 28.58/28.78  thf('71', plain,
% 28.58/28.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 28.58/28.78      inference('sup+', [status(thm)], ['69', '70'])).
% 28.58/28.78  thf(t92_xboole_1, axiom,
% 28.58/28.78    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 28.58/28.78  thf('72', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 28.58/28.78      inference('cnf', [status(esa)], [t92_xboole_1])).
% 28.58/28.78  thf('73', plain, (![X38 : $i]: ((k1_xboole_0) != (k1_tarski @ X38))),
% 28.58/28.78      inference('demod', [status(thm)], ['68', '71', '72'])).
% 28.58/28.78  thf('74', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         ((k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0))),
% 28.58/28.78      inference('clc', [status(thm)], ['66', '73'])).
% 28.58/28.78  thf('75', plain,
% 28.58/28.78      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ (k1_tarski @ k1_xboole_0))
% 28.58/28.78         = (sk_B))),
% 28.58/28.78      inference('simplify_reflect-', [status(thm)], ['63', '74'])).
% 28.58/28.78  thf('76', plain,
% 28.58/28.78      (![X0 : $i]:
% 28.58/28.78         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)))
% 28.58/28.78           = (k1_tarski @ k1_xboole_0))),
% 28.58/28.78      inference('sup-', [status(thm)], ['8', '9'])).
% 28.58/28.78  thf('77', plain,
% 28.58/28.78      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B) = (k1_tarski @ k1_xboole_0))),
% 28.58/28.78      inference('sup+', [status(thm)], ['75', '76'])).
% 28.58/28.78  thf('78', plain,
% 28.58/28.78      (((k7_setfam_1 @ sk_A @ sk_B) != (k1_tarski @ k1_xboole_0))),
% 28.58/28.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.58/28.78  thf('79', plain, (((k1_setfam_1 @ sk_B) = (sk_A))),
% 28.58/28.78      inference('sup+', [status(thm)], ['12', '17'])).
% 28.58/28.78  thf('80', plain,
% 28.58/28.78      (((k7_setfam_1 @ (k1_setfam_1 @ sk_B) @ sk_B)
% 28.58/28.78         != (k1_tarski @ k1_xboole_0))),
% 28.58/28.78      inference('demod', [status(thm)], ['78', '79'])).
% 28.58/28.78  thf('81', plain, ($false),
% 28.58/28.78      inference('simplify_reflect-', [status(thm)], ['77', '80'])).
% 28.58/28.78  
% 28.58/28.78  % SZS output end Refutation
% 28.58/28.78  
% 28.58/28.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
