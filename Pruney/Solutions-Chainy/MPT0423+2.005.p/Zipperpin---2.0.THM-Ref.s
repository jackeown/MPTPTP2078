%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NEbXX0zJwd

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:16 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 182 expanded)
%              Number of leaves         :   39 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  784 (1352 expanded)
%              Number of equality atoms :   64 ( 110 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X43: $i] :
      ( ( k1_subset_1 @ X43 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X67: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X67 ) @ ( k1_zfmisc_1 @ X67 ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
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
    ! [X68: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X68 ) ) ),
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
    ! [X70: $i,X71: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X70 ) @ ( k1_zfmisc_1 @ X71 ) )
      | ~ ( r2_hidden @ X70 @ X71 ) ) ),
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
    ! [X74: $i,X75: $i] :
      ( ( ( k7_setfam_1 @ X75 @ ( k7_setfam_1 @ X75 @ X74 ) )
        = X74 )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X75 ) ) ) ) ),
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

thf(t51_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('12',plain,(
    ! [X84: $i,X85: $i,X86: $i] :
      ( ~ ( m1_subset_1 @ X84 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X85 ) ) )
      | ( r1_tarski @ X86 @ X84 )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X85 @ X86 ) @ ( k7_setfam_1 @ X85 @ X84 ) )
      | ~ ( m1_subset_1 @ X86 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X85 ) ) ) ) ),
    inference(cnf,[status(esa)],[t51_setfam_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X43: $i] :
      ( ( k1_subset_1 @ X43 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X69: $i] :
      ( ( k2_subset_1 @ X69 )
      = ( k3_subset_1 @ X69 @ ( k1_subset_1 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('17',plain,(
    ! [X44: $i] :
      ( ( k2_subset_1 @ X44 )
      = X44 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('18',plain,(
    ! [X69: $i] :
      ( X69
      = ( k3_subset_1 @ X69 @ ( k1_subset_1 @ X69 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X72: $i,X73: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X72 @ X73 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X72 ) ) )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X72 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('22',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X81: $i,X82: $i,X83: $i] :
      ( ~ ( m1_subset_1 @ X81 @ ( k1_zfmisc_1 @ X82 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X82 @ X81 ) @ ( k7_setfam_1 @ X82 @ X83 ) )
      | ( r2_hidden @ X81 @ X83 )
      | ~ ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X82 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X74: $i,X75: $i] :
      ( ( ( k7_setfam_1 @ X75 @ ( k7_setfam_1 @ X75 @ X74 ) )
        = X74 )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X75 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('27',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ k1_xboole_0 @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('31',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ ( k1_tarski @ X39 ) )
      | ( X38
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('32',plain,(
    ! [X39: $i] :
      ( r1_tarski @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X39 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('37',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ~ ( r1_tarski @ ( k1_tarski @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('41',plain,(
    r2_hidden @ k1_xboole_0 @ ( k7_setfam_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','39','40'])).

thf('42',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X31 ) @ X33 )
      | ~ ( r2_hidden @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('43',plain,(
    r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('46',plain,(
    ! [X72: $i,X73: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X72 @ X73 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X72 ) ) )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X72 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) ) @ sk_B ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38
        = ( k1_tarski @ X37 ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( r1_tarski @ X38 @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) )
      = sk_B )
    | ( ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t46_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('56',plain,(
    ! [X79: $i,X80: $i] :
      ( ( ( k7_setfam_1 @ X79 @ X80 )
       != k1_xboole_0 )
      | ( X80 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X79 ) ) ) ) ),
    inference(cnf,[status(esa)],[t46_setfam_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('58',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 != X34 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X34 ) )
       != ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('59',plain,(
    ! [X34: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X34 ) )
     != ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('60',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('61',plain,(
    ! [X76: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X76 ) )
      = X76 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X77: $i,X78: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X77 @ X78 ) )
      = ( k3_xboole_0 @ X77 @ X78 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('67',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('68',plain,(
    ! [X34: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X34 ) ) ),
    inference(demod,[status(thm)],['59','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['57','68'])).

thf('70',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k1_tarski @ k1_xboole_0 ) )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['54','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) ) )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('72',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ( k7_setfam_1 @ sk_A @ sk_B )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NEbXX0zJwd
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:50:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.74/1.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.96  % Solved by: fo/fo7.sh
% 1.74/1.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.96  % done 2699 iterations in 1.496s
% 1.74/1.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.96  % SZS output start Refutation
% 1.74/1.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.74/1.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.74/1.96  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.96  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.74/1.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.74/1.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 1.74/1.96  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.74/1.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.74/1.96  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.74/1.96  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.74/1.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.96  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.74/1.96  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.74/1.96  thf('0', plain, (![X43 : $i]: ((k1_subset_1 @ X43) = (k1_xboole_0))),
% 1.74/1.96      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.74/1.96  thf(dt_k1_subset_1, axiom,
% 1.74/1.96    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.74/1.96  thf('1', plain,
% 1.74/1.96      (![X67 : $i]: (m1_subset_1 @ (k1_subset_1 @ X67) @ (k1_zfmisc_1 @ X67))),
% 1.74/1.96      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 1.74/1.96  thf('2', plain,
% 1.74/1.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['0', '1'])).
% 1.74/1.96  thf(d2_subset_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( ( v1_xboole_0 @ A ) =>
% 1.74/1.96         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.74/1.96       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.74/1.96         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.74/1.96  thf('3', plain,
% 1.74/1.96      (![X40 : $i, X41 : $i]:
% 1.74/1.96         (~ (m1_subset_1 @ X40 @ X41)
% 1.74/1.96          | (r2_hidden @ X40 @ X41)
% 1.74/1.96          | (v1_xboole_0 @ X41))),
% 1.74/1.96      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.74/1.96  thf('4', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.74/1.96          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['2', '3'])).
% 1.74/1.96  thf(fc1_subset_1, axiom,
% 1.74/1.96    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.74/1.96  thf('5', plain, (![X68 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X68))),
% 1.74/1.96      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.74/1.96  thf('6', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.74/1.96      inference('clc', [status(thm)], ['4', '5'])).
% 1.74/1.96  thf(t63_subset_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( r2_hidden @ A @ B ) =>
% 1.74/1.96       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.74/1.96  thf('7', plain,
% 1.74/1.96      (![X70 : $i, X71 : $i]:
% 1.74/1.96         ((m1_subset_1 @ (k1_tarski @ X70) @ (k1_zfmisc_1 @ X71))
% 1.74/1.96          | ~ (r2_hidden @ X70 @ X71))),
% 1.74/1.96      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.74/1.96  thf('8', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.74/1.96          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['6', '7'])).
% 1.74/1.96  thf(involutiveness_k7_setfam_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.74/1.96       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 1.74/1.96  thf('9', plain,
% 1.74/1.96      (![X74 : $i, X75 : $i]:
% 1.74/1.96         (((k7_setfam_1 @ X75 @ (k7_setfam_1 @ X75 @ X74)) = (X74))
% 1.74/1.96          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X75))))),
% 1.74/1.96      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 1.74/1.96  thf('10', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)))
% 1.74/1.96           = (k1_tarski @ k1_xboole_0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['8', '9'])).
% 1.74/1.96  thf(t55_setfam_1, conjecture,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.74/1.96       ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 1.74/1.96         ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ))).
% 1.74/1.96  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.96    (~( ![A:$i,B:$i]:
% 1.74/1.96        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.74/1.96          ( ( ( B ) = ( k1_tarski @ A ) ) =>
% 1.74/1.96            ( ( k7_setfam_1 @ A @ B ) = ( k1_tarski @ k1_xboole_0 ) ) ) ) )),
% 1.74/1.96    inference('cnf.neg', [status(esa)], [t55_setfam_1])).
% 1.74/1.96  thf('11', plain,
% 1.74/1.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf(t51_setfam_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.74/1.96       ( ![C:$i]:
% 1.74/1.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.74/1.96           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 1.74/1.96             ( r1_tarski @ B @ C ) ) ) ) ))).
% 1.74/1.96  thf('12', plain,
% 1.74/1.96      (![X84 : $i, X85 : $i, X86 : $i]:
% 1.74/1.96         (~ (m1_subset_1 @ X84 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X85)))
% 1.74/1.96          | (r1_tarski @ X86 @ X84)
% 1.74/1.96          | ~ (r1_tarski @ (k7_setfam_1 @ X85 @ X86) @ 
% 1.74/1.96               (k7_setfam_1 @ X85 @ X84))
% 1.74/1.96          | ~ (m1_subset_1 @ X86 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X85))))),
% 1.74/1.96      inference('cnf', [status(esa)], [t51_setfam_1])).
% 1.74/1.96  thf('13', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.74/1.96          | ~ (r1_tarski @ (k7_setfam_1 @ sk_A @ X0) @ 
% 1.74/1.96               (k7_setfam_1 @ sk_A @ sk_B))
% 1.74/1.96          | (r1_tarski @ X0 @ sk_B))),
% 1.74/1.96      inference('sup-', [status(thm)], ['11', '12'])).
% 1.74/1.96  thf('14', plain,
% 1.74/1.96      ((~ (r1_tarski @ (k1_tarski @ k1_xboole_0) @ (k7_setfam_1 @ sk_A @ sk_B))
% 1.74/1.96        | (r1_tarski @ (k7_setfam_1 @ sk_A @ (k1_tarski @ k1_xboole_0)) @ sk_B)
% 1.74/1.96        | ~ (m1_subset_1 @ (k7_setfam_1 @ sk_A @ (k1_tarski @ k1_xboole_0)) @ 
% 1.74/1.96             (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['10', '13'])).
% 1.74/1.96  thf('15', plain, (![X43 : $i]: ((k1_subset_1 @ X43) = (k1_xboole_0))),
% 1.74/1.96      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.74/1.96  thf(t22_subset_1, axiom,
% 1.74/1.96    (![A:$i]:
% 1.74/1.96     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 1.74/1.96  thf('16', plain,
% 1.74/1.96      (![X69 : $i]:
% 1.74/1.96         ((k2_subset_1 @ X69) = (k3_subset_1 @ X69 @ (k1_subset_1 @ X69)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t22_subset_1])).
% 1.74/1.96  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.74/1.96  thf('17', plain, (![X44 : $i]: ((k2_subset_1 @ X44) = (X44))),
% 1.74/1.96      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.74/1.96  thf('18', plain,
% 1.74/1.96      (![X69 : $i]: ((X69) = (k3_subset_1 @ X69 @ (k1_subset_1 @ X69)))),
% 1.74/1.96      inference('demod', [status(thm)], ['16', '17'])).
% 1.74/1.96  thf('19', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['15', '18'])).
% 1.74/1.96  thf('20', plain,
% 1.74/1.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf(dt_k7_setfam_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.74/1.96       ( m1_subset_1 @
% 1.74/1.96         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.74/1.96  thf('21', plain,
% 1.74/1.96      (![X72 : $i, X73 : $i]:
% 1.74/1.96         ((m1_subset_1 @ (k7_setfam_1 @ X72 @ X73) @ 
% 1.74/1.96           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X72)))
% 1.74/1.96          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X72))))),
% 1.74/1.96      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 1.74/1.96  thf('22', plain,
% 1.74/1.96      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 1.74/1.96        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['20', '21'])).
% 1.74/1.96  thf(t49_setfam_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.74/1.96       ( ![C:$i]:
% 1.74/1.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.74/1.96           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 1.74/1.96             ( r2_hidden @ C @ B ) ) ) ) ))).
% 1.74/1.96  thf('23', plain,
% 1.74/1.96      (![X81 : $i, X82 : $i, X83 : $i]:
% 1.74/1.96         (~ (m1_subset_1 @ X81 @ (k1_zfmisc_1 @ X82))
% 1.74/1.96          | ~ (r2_hidden @ (k3_subset_1 @ X82 @ X81) @ 
% 1.74/1.96               (k7_setfam_1 @ X82 @ X83))
% 1.74/1.96          | (r2_hidden @ X81 @ X83)
% 1.74/1.96          | ~ (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X82))))),
% 1.74/1.96      inference('cnf', [status(esa)], [t49_setfam_1])).
% 1.74/1.96  thf('24', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 1.74/1.96          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 1.74/1.96               (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 1.74/1.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['22', '23'])).
% 1.74/1.96  thf('25', plain,
% 1.74/1.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf('26', plain,
% 1.74/1.96      (![X74 : $i, X75 : $i]:
% 1.74/1.96         (((k7_setfam_1 @ X75 @ (k7_setfam_1 @ X75 @ X74)) = (X74))
% 1.74/1.96          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X75))))),
% 1.74/1.96      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 1.74/1.96  thf('27', plain,
% 1.74/1.96      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.74/1.96      inference('sup-', [status(thm)], ['25', '26'])).
% 1.74/1.96  thf('28', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 1.74/1.96          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 1.74/1.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.74/1.96      inference('demod', [status(thm)], ['24', '27'])).
% 1.74/1.96  thf('29', plain,
% 1.74/1.96      ((~ (r2_hidden @ sk_A @ sk_B)
% 1.74/1.96        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.74/1.96        | (r2_hidden @ k1_xboole_0 @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['19', '28'])).
% 1.74/1.96  thf('30', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf(t39_zfmisc_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.74/1.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.74/1.96  thf('31', plain,
% 1.74/1.96      (![X38 : $i, X39 : $i]:
% 1.74/1.96         ((r1_tarski @ X38 @ (k1_tarski @ X39)) | ((X38) != (k1_tarski @ X39)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 1.74/1.96  thf('32', plain,
% 1.74/1.96      (![X39 : $i]: (r1_tarski @ (k1_tarski @ X39) @ (k1_tarski @ X39))),
% 1.74/1.96      inference('simplify', [status(thm)], ['31'])).
% 1.74/1.96  thf('33', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 1.74/1.96      inference('sup+', [status(thm)], ['30', '32'])).
% 1.74/1.96  thf('34', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf('35', plain, ((r1_tarski @ sk_B @ sk_B)),
% 1.74/1.96      inference('demod', [status(thm)], ['33', '34'])).
% 1.74/1.96  thf('36', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf(l1_zfmisc_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.74/1.96  thf('37', plain,
% 1.74/1.96      (![X31 : $i, X32 : $i]:
% 1.74/1.96         ((r2_hidden @ X31 @ X32) | ~ (r1_tarski @ (k1_tarski @ X31) @ X32))),
% 1.74/1.96      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.74/1.96  thf('38', plain,
% 1.74/1.96      (![X0 : $i]: (~ (r1_tarski @ sk_B @ X0) | (r2_hidden @ sk_A @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['36', '37'])).
% 1.74/1.96  thf('39', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.74/1.96      inference('sup-', [status(thm)], ['35', '38'])).
% 1.74/1.96  thf('40', plain,
% 1.74/1.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['0', '1'])).
% 1.74/1.96  thf('41', plain, ((r2_hidden @ k1_xboole_0 @ (k7_setfam_1 @ sk_A @ sk_B))),
% 1.74/1.96      inference('demod', [status(thm)], ['29', '39', '40'])).
% 1.74/1.96  thf('42', plain,
% 1.74/1.96      (![X31 : $i, X33 : $i]:
% 1.74/1.96         ((r1_tarski @ (k1_tarski @ X31) @ X33) | ~ (r2_hidden @ X31 @ X33))),
% 1.74/1.96      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.74/1.96  thf('43', plain,
% 1.74/1.96      ((r1_tarski @ (k1_tarski @ k1_xboole_0) @ (k7_setfam_1 @ sk_A @ sk_B))),
% 1.74/1.96      inference('sup-', [status(thm)], ['41', '42'])).
% 1.74/1.96  thf('44', plain,
% 1.74/1.96      (((r1_tarski @ (k7_setfam_1 @ sk_A @ (k1_tarski @ k1_xboole_0)) @ sk_B)
% 1.74/1.96        | ~ (m1_subset_1 @ (k7_setfam_1 @ sk_A @ (k1_tarski @ k1_xboole_0)) @ 
% 1.74/1.96             (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['14', '43'])).
% 1.74/1.96  thf('45', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.74/1.96          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['6', '7'])).
% 1.74/1.96  thf('46', plain,
% 1.74/1.96      (![X72 : $i, X73 : $i]:
% 1.74/1.96         ((m1_subset_1 @ (k7_setfam_1 @ X72 @ X73) @ 
% 1.74/1.96           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X72)))
% 1.74/1.96          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X72))))),
% 1.74/1.96      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 1.74/1.96  thf('47', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (m1_subset_1 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) @ 
% 1.74/1.96          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['45', '46'])).
% 1.74/1.96  thf('48', plain,
% 1.74/1.96      ((r1_tarski @ (k7_setfam_1 @ sk_A @ (k1_tarski @ k1_xboole_0)) @ sk_B)),
% 1.74/1.96      inference('demod', [status(thm)], ['44', '47'])).
% 1.74/1.96  thf('49', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf('50', plain,
% 1.74/1.96      (![X37 : $i, X38 : $i]:
% 1.74/1.96         (((X38) = (k1_tarski @ X37))
% 1.74/1.96          | ((X38) = (k1_xboole_0))
% 1.74/1.96          | ~ (r1_tarski @ X38 @ (k1_tarski @ X37)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 1.74/1.96  thf('51', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (~ (r1_tarski @ X0 @ sk_B)
% 1.74/1.96          | ((X0) = (k1_xboole_0))
% 1.74/1.96          | ((X0) = (k1_tarski @ sk_A)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['49', '50'])).
% 1.74/1.96  thf('52', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf('53', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 1.74/1.96      inference('demod', [status(thm)], ['51', '52'])).
% 1.74/1.96  thf('54', plain,
% 1.74/1.96      ((((k7_setfam_1 @ sk_A @ (k1_tarski @ k1_xboole_0)) = (sk_B))
% 1.74/1.96        | ((k7_setfam_1 @ sk_A @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['48', '53'])).
% 1.74/1.96  thf('55', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 1.74/1.96          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['6', '7'])).
% 1.74/1.96  thf(t46_setfam_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.74/1.96       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.74/1.96            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.74/1.96  thf('56', plain,
% 1.74/1.96      (![X79 : $i, X80 : $i]:
% 1.74/1.96         (((k7_setfam_1 @ X79 @ X80) != (k1_xboole_0))
% 1.74/1.96          | ((X80) = (k1_xboole_0))
% 1.74/1.96          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X79))))),
% 1.74/1.96      inference('cnf', [status(esa)], [t46_setfam_1])).
% 1.74/1.96  thf('57', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 1.74/1.96          | ((k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['55', '56'])).
% 1.74/1.96  thf(t20_zfmisc_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.74/1.96         ( k1_tarski @ A ) ) <=>
% 1.74/1.96       ( ( A ) != ( B ) ) ))).
% 1.74/1.96  thf('58', plain,
% 1.74/1.96      (![X34 : $i, X35 : $i]:
% 1.74/1.96         (((X35) != (X34))
% 1.74/1.96          | ((k4_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X34))
% 1.74/1.96              != (k1_tarski @ X35)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.74/1.96  thf('59', plain,
% 1.74/1.96      (![X34 : $i]:
% 1.74/1.96         ((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X34))
% 1.74/1.96           != (k1_tarski @ X34))),
% 1.74/1.96      inference('simplify', [status(thm)], ['58'])).
% 1.74/1.96  thf(t69_enumset1, axiom,
% 1.74/1.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.74/1.96  thf('60', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 1.74/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.74/1.96  thf(t11_setfam_1, axiom,
% 1.74/1.96    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 1.74/1.96  thf('61', plain, (![X76 : $i]: ((k1_setfam_1 @ (k1_tarski @ X76)) = (X76))),
% 1.74/1.96      inference('cnf', [status(esa)], [t11_setfam_1])).
% 1.74/1.96  thf('62', plain,
% 1.74/1.96      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['60', '61'])).
% 1.74/1.96  thf(t12_setfam_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.74/1.96  thf('63', plain,
% 1.74/1.96      (![X77 : $i, X78 : $i]:
% 1.74/1.96         ((k1_setfam_1 @ (k2_tarski @ X77 @ X78)) = (k3_xboole_0 @ X77 @ X78))),
% 1.74/1.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.74/1.96  thf('64', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.74/1.96      inference('demod', [status(thm)], ['62', '63'])).
% 1.74/1.96  thf(t100_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.74/1.96  thf('65', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k4_xboole_0 @ X0 @ X1)
% 1.74/1.96           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.96  thf('66', plain,
% 1.74/1.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['64', '65'])).
% 1.74/1.96  thf(t92_xboole_1, axiom,
% 1.74/1.96    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.74/1.96  thf('67', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 1.74/1.96      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.74/1.96  thf('68', plain, (![X34 : $i]: ((k1_xboole_0) != (k1_tarski @ X34))),
% 1.74/1.96      inference('demod', [status(thm)], ['59', '66', '67'])).
% 1.74/1.96  thf('69', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0))),
% 1.74/1.96      inference('clc', [status(thm)], ['57', '68'])).
% 1.74/1.96  thf('70', plain,
% 1.74/1.96      (((k7_setfam_1 @ sk_A @ (k1_tarski @ k1_xboole_0)) = (sk_B))),
% 1.74/1.96      inference('simplify_reflect-', [status(thm)], ['54', '69'])).
% 1.74/1.96  thf('71', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ (k1_tarski @ k1_xboole_0)))
% 1.74/1.96           = (k1_tarski @ k1_xboole_0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['8', '9'])).
% 1.74/1.96  thf('72', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_tarski @ k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['70', '71'])).
% 1.74/1.96  thf('73', plain,
% 1.74/1.96      (((k7_setfam_1 @ sk_A @ sk_B) != (k1_tarski @ k1_xboole_0))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf('74', plain, ($false),
% 1.74/1.96      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 1.74/1.96  
% 1.74/1.96  % SZS output end Refutation
% 1.74/1.96  
% 1.74/1.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
