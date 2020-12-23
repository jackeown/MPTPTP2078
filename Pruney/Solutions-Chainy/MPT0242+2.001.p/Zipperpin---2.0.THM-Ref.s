%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IOwNwryArc

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:08 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 181 expanded)
%              Number of leaves         :   32 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  768 (1289 expanded)
%              Number of equality atoms :   74 ( 129 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t37_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t37_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X86: $i,X87: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X86 @ X87 ) )
      = ( k2_xboole_0 @ X86 @ X87 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('10',plain,(
    ! [X86: $i,X87: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X86 @ X87 ) )
      = ( k2_xboole_0 @ X86 @ X87 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X39: $i] :
      ( ( k5_xboole_0 @ X39 @ X39 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X24: $i] :
      ( ( k3_xboole_0 @ X24 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['5','18'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X80: $i,X82: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X80 ) @ X82 )
        = ( k1_tarski @ X80 ) )
      | ( r2_hidden @ X80 @ X82 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('21',plain,
    ( ( ( k1_xboole_0
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('22',plain,(
    ! [X84: $i,X85: $i] :
      ( ( r1_tarski @ X84 @ ( k1_tarski @ X85 ) )
      | ( X84 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('23',plain,(
    ! [X85: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X85 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r2_hidden @ X78 @ X79 )
      | ( ( k3_xboole_0 @ X79 @ ( k1_tarski @ X78 ) )
       != ( k1_tarski @ X78 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X24: $i] :
      ( ( k3_xboole_0 @ X24 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('31',plain,(
    ! [X33: $i] :
      ( r1_xboole_0 @ X33 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('32',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['27','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['21','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X34: $i,X35: $i] :
      ( r1_tarski @ X34 @ ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X83: $i,X84: $i] :
      ( ( X84
        = ( k1_tarski @ X83 ) )
      | ( X84 = k1_xboole_0 )
      | ~ ( r1_tarski @ X84 @ ( k1_tarski @ X83 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X80: $i,X81: $i] :
      ( ~ ( r2_hidden @ X80 @ X81 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X80 ) @ X81 )
       != ( k1_tarski @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('51',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26 = X25 )
      | ( ( k4_xboole_0 @ X26 @ X25 )
       != ( k4_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('54',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('57',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('58',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k3_xboole_0 @ X31 @ X32 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X30 @ X31 ) @ ( k4_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('59',plain,(
    ! [X86: $i,X87: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X86 @ X87 ) )
      = ( k2_xboole_0 @ X86 @ X87 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('60',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k3_xboole_0 @ X31 @ X32 ) )
      = ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ ( k4_xboole_0 @ X30 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('62',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('63',plain,(
    ! [X86: $i,X87: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X86 @ X87 ) )
      = ( k2_xboole_0 @ X86 @ X87 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('64',plain,(
    ! [X16: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ k1_xboole_0 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','65'])).

thf('67',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['49','66'])).

thf('68',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('70',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k2_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('71',plain,(
    ! [X86: $i,X87: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X86 @ X87 ) )
      = ( k2_xboole_0 @ X86 @ X87 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('72',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k3_tarski @ ( k2_tarski @ X21 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IOwNwryArc
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:27:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.34/1.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.34/1.57  % Solved by: fo/fo7.sh
% 1.34/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.34/1.57  % done 2395 iterations in 1.096s
% 1.34/1.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.34/1.57  % SZS output start Refutation
% 1.34/1.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.34/1.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.34/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.34/1.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.34/1.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.34/1.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.34/1.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.34/1.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.34/1.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.34/1.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.34/1.57  thf(sk_B_type, type, sk_B: $i).
% 1.34/1.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.34/1.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.34/1.57  thf(t37_zfmisc_1, conjecture,
% 1.34/1.57    (![A:$i,B:$i]:
% 1.34/1.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.34/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.34/1.57    (~( ![A:$i,B:$i]:
% 1.34/1.57        ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ) )),
% 1.34/1.57    inference('cnf.neg', [status(esa)], [t37_zfmisc_1])).
% 1.34/1.57  thf('0', plain,
% 1.34/1.57      ((~ (r2_hidden @ sk_A @ sk_B) | ~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.34/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.57  thf('1', plain,
% 1.34/1.57      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.34/1.57       ~ ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.34/1.57      inference('split', [status(esa)], ['0'])).
% 1.34/1.57  thf('2', plain,
% 1.34/1.57      (((r2_hidden @ sk_A @ sk_B) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.34/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.57  thf('3', plain,
% 1.34/1.57      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 1.34/1.57         <= (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.34/1.57      inference('split', [status(esa)], ['2'])).
% 1.34/1.57  thf(t28_xboole_1, axiom,
% 1.34/1.57    (![A:$i,B:$i]:
% 1.34/1.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.34/1.57  thf('4', plain,
% 1.34/1.57      (![X19 : $i, X20 : $i]:
% 1.34/1.57         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 1.34/1.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.34/1.57  thf('5', plain,
% 1.34/1.57      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 1.34/1.57         <= (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.34/1.57      inference('sup-', [status(thm)], ['3', '4'])).
% 1.34/1.57  thf(d6_xboole_0, axiom,
% 1.34/1.57    (![A:$i,B:$i]:
% 1.34/1.57     ( ( k5_xboole_0 @ A @ B ) =
% 1.34/1.57       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.34/1.57  thf('6', plain,
% 1.34/1.57      (![X6 : $i, X7 : $i]:
% 1.34/1.57         ((k5_xboole_0 @ X6 @ X7)
% 1.34/1.57           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X7 @ X6)))),
% 1.34/1.57      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.34/1.57  thf(l51_zfmisc_1, axiom,
% 1.34/1.57    (![A:$i,B:$i]:
% 1.34/1.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.34/1.57  thf('7', plain,
% 1.34/1.57      (![X86 : $i, X87 : $i]:
% 1.34/1.57         ((k3_tarski @ (k2_tarski @ X86 @ X87)) = (k2_xboole_0 @ X86 @ X87))),
% 1.34/1.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.34/1.57  thf('8', plain,
% 1.34/1.57      (![X6 : $i, X7 : $i]:
% 1.34/1.57         ((k5_xboole_0 @ X6 @ X7)
% 1.34/1.57           = (k3_tarski @ 
% 1.34/1.57              (k2_tarski @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X7 @ X6))))),
% 1.34/1.57      inference('demod', [status(thm)], ['6', '7'])).
% 1.34/1.57  thf(idempotence_k2_xboole_0, axiom,
% 1.34/1.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.34/1.57  thf('9', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 1.34/1.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.34/1.57  thf('10', plain,
% 1.34/1.57      (![X86 : $i, X87 : $i]:
% 1.34/1.57         ((k3_tarski @ (k2_tarski @ X86 @ X87)) = (k2_xboole_0 @ X86 @ X87))),
% 1.34/1.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.34/1.57  thf('11', plain, (![X8 : $i]: ((k3_tarski @ (k2_tarski @ X8 @ X8)) = (X8))),
% 1.34/1.57      inference('demod', [status(thm)], ['9', '10'])).
% 1.34/1.57  thf('12', plain,
% 1.34/1.57      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.34/1.57      inference('sup+', [status(thm)], ['8', '11'])).
% 1.34/1.57  thf(t49_xboole_1, axiom,
% 1.34/1.57    (![A:$i,B:$i,C:$i]:
% 1.34/1.57     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.34/1.57       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.34/1.57  thf('13', plain,
% 1.34/1.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.34/1.57         ((k3_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 1.34/1.57           = (k4_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ X29))),
% 1.34/1.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.34/1.57  thf('14', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 1.34/1.57           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.34/1.57      inference('sup+', [status(thm)], ['12', '13'])).
% 1.34/1.57  thf(t92_xboole_1, axiom,
% 1.34/1.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.34/1.57  thf('15', plain, (![X39 : $i]: ((k5_xboole_0 @ X39 @ X39) = (k1_xboole_0))),
% 1.34/1.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.34/1.57  thf(t2_boole, axiom,
% 1.34/1.57    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.34/1.57  thf('16', plain,
% 1.34/1.57      (![X24 : $i]: ((k3_xboole_0 @ X24 @ k1_xboole_0) = (k1_xboole_0))),
% 1.34/1.57      inference('cnf', [status(esa)], [t2_boole])).
% 1.34/1.57  thf('17', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 1.34/1.57      inference('sup+', [status(thm)], ['15', '16'])).
% 1.34/1.57  thf('18', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.34/1.57      inference('demod', [status(thm)], ['14', '17'])).
% 1.34/1.57  thf('19', plain,
% 1.34/1.57      ((((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 1.34/1.57         <= (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.34/1.57      inference('sup+', [status(thm)], ['5', '18'])).
% 1.34/1.57  thf(l33_zfmisc_1, axiom,
% 1.34/1.57    (![A:$i,B:$i]:
% 1.34/1.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 1.34/1.57       ( ~( r2_hidden @ A @ B ) ) ))).
% 1.34/1.57  thf('20', plain,
% 1.34/1.57      (![X80 : $i, X82 : $i]:
% 1.34/1.57         (((k4_xboole_0 @ (k1_tarski @ X80) @ X82) = (k1_tarski @ X80))
% 1.34/1.57          | (r2_hidden @ X80 @ X82))),
% 1.34/1.57      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 1.34/1.57  thf('21', plain,
% 1.34/1.57      (((((k1_xboole_0) = (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 1.34/1.57         <= (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.34/1.57      inference('sup+', [status(thm)], ['19', '20'])).
% 1.34/1.57  thf(l3_zfmisc_1, axiom,
% 1.34/1.57    (![A:$i,B:$i]:
% 1.34/1.57     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.34/1.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.34/1.57  thf('22', plain,
% 1.34/1.57      (![X84 : $i, X85 : $i]:
% 1.34/1.57         ((r1_tarski @ X84 @ (k1_tarski @ X85)) | ((X84) != (k1_xboole_0)))),
% 1.34/1.57      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.34/1.57  thf('23', plain,
% 1.34/1.57      (![X85 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X85))),
% 1.34/1.57      inference('simplify', [status(thm)], ['22'])).
% 1.34/1.57  thf('24', plain,
% 1.34/1.57      (![X19 : $i, X20 : $i]:
% 1.34/1.57         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 1.34/1.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.34/1.57  thf('25', plain,
% 1.34/1.57      (![X0 : $i]:
% 1.34/1.57         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 1.34/1.57      inference('sup-', [status(thm)], ['23', '24'])).
% 1.34/1.57  thf(l29_zfmisc_1, axiom,
% 1.34/1.57    (![A:$i,B:$i]:
% 1.34/1.57     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 1.34/1.57       ( r2_hidden @ B @ A ) ))).
% 1.34/1.57  thf('26', plain,
% 1.34/1.57      (![X78 : $i, X79 : $i]:
% 1.34/1.57         ((r2_hidden @ X78 @ X79)
% 1.34/1.57          | ((k3_xboole_0 @ X79 @ (k1_tarski @ X78)) != (k1_tarski @ X78)))),
% 1.34/1.57      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 1.34/1.57  thf('27', plain,
% 1.34/1.57      (![X0 : $i]:
% 1.34/1.57         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 1.34/1.57      inference('sup-', [status(thm)], ['25', '26'])).
% 1.34/1.57  thf('28', plain,
% 1.34/1.57      (![X24 : $i]: ((k3_xboole_0 @ X24 @ k1_xboole_0) = (k1_xboole_0))),
% 1.34/1.57      inference('cnf', [status(esa)], [t2_boole])).
% 1.34/1.57  thf(t4_xboole_0, axiom,
% 1.34/1.57    (![A:$i,B:$i]:
% 1.34/1.57     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.34/1.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.34/1.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.34/1.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.34/1.57  thf('29', plain,
% 1.34/1.57      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.34/1.57         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 1.34/1.57          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.34/1.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.34/1.57  thf('30', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.34/1.57      inference('sup-', [status(thm)], ['28', '29'])).
% 1.34/1.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.34/1.57  thf('31', plain, (![X33 : $i]: (r1_xboole_0 @ X33 @ k1_xboole_0)),
% 1.34/1.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.34/1.57  thf('32', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.34/1.57      inference('demod', [status(thm)], ['30', '31'])).
% 1.34/1.57  thf('33', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 1.34/1.57      inference('clc', [status(thm)], ['27', '32'])).
% 1.34/1.57  thf('34', plain,
% 1.34/1.57      (((r2_hidden @ sk_A @ sk_B))
% 1.34/1.57         <= (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.34/1.57      inference('clc', [status(thm)], ['21', '33'])).
% 1.34/1.57  thf('35', plain,
% 1.34/1.57      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.34/1.57      inference('split', [status(esa)], ['0'])).
% 1.34/1.57  thf('36', plain,
% 1.34/1.57      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.34/1.57       ~ ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.34/1.57      inference('sup-', [status(thm)], ['34', '35'])).
% 1.34/1.57  thf('37', plain,
% 1.34/1.57      (((r2_hidden @ sk_A @ sk_B)) | ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.34/1.57      inference('split', [status(esa)], ['2'])).
% 1.34/1.57  thf('38', plain,
% 1.34/1.57      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.34/1.57      inference('split', [status(esa)], ['2'])).
% 1.34/1.57  thf('39', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 1.34/1.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.34/1.57  thf(t7_xboole_1, axiom,
% 1.34/1.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.34/1.57  thf('40', plain,
% 1.34/1.57      (![X34 : $i, X35 : $i]: (r1_tarski @ X34 @ (k2_xboole_0 @ X34 @ X35))),
% 1.34/1.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.34/1.57  thf('41', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.34/1.57      inference('sup+', [status(thm)], ['39', '40'])).
% 1.34/1.57  thf(t106_xboole_1, axiom,
% 1.34/1.57    (![A:$i,B:$i,C:$i]:
% 1.34/1.57     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.34/1.57       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.34/1.57  thf('42', plain,
% 1.34/1.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.34/1.57         ((r1_tarski @ X13 @ X14)
% 1.34/1.57          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 1.34/1.57      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.34/1.57  thf('43', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 1.34/1.57      inference('sup-', [status(thm)], ['41', '42'])).
% 1.34/1.57  thf('44', plain,
% 1.34/1.57      (![X83 : $i, X84 : $i]:
% 1.34/1.57         (((X84) = (k1_tarski @ X83))
% 1.34/1.57          | ((X84) = (k1_xboole_0))
% 1.34/1.57          | ~ (r1_tarski @ X84 @ (k1_tarski @ X83)))),
% 1.34/1.57      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.34/1.57  thf('45', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 1.34/1.57          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.34/1.57      inference('sup-', [status(thm)], ['43', '44'])).
% 1.34/1.57  thf('46', plain,
% 1.34/1.57      (![X80 : $i, X81 : $i]:
% 1.34/1.57         (~ (r2_hidden @ X80 @ X81)
% 1.34/1.57          | ((k4_xboole_0 @ (k1_tarski @ X80) @ X81) != (k1_tarski @ X80)))),
% 1.34/1.57      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 1.34/1.57  thf('47', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 1.34/1.57          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 1.34/1.57          | ~ (r2_hidden @ X0 @ X1))),
% 1.34/1.57      inference('sup-', [status(thm)], ['45', '46'])).
% 1.34/1.57  thf('48', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         (~ (r2_hidden @ X0 @ X1)
% 1.34/1.57          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 1.34/1.57      inference('simplify', [status(thm)], ['47'])).
% 1.34/1.57  thf('49', plain,
% 1.34/1.57      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 1.34/1.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.34/1.57      inference('sup-', [status(thm)], ['38', '48'])).
% 1.34/1.57  thf('50', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.34/1.57      inference('demod', [status(thm)], ['14', '17'])).
% 1.34/1.57  thf(t32_xboole_1, axiom,
% 1.34/1.57    (![A:$i,B:$i]:
% 1.34/1.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 1.34/1.57       ( ( A ) = ( B ) ) ))).
% 1.34/1.57  thf('51', plain,
% 1.34/1.57      (![X25 : $i, X26 : $i]:
% 1.34/1.57         (((X26) = (X25))
% 1.34/1.57          | ((k4_xboole_0 @ X26 @ X25) != (k4_xboole_0 @ X25 @ X26)))),
% 1.34/1.57      inference('cnf', [status(esa)], [t32_xboole_1])).
% 1.34/1.57  thf('52', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         (((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.34/1.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.34/1.57      inference('sup-', [status(thm)], ['50', '51'])).
% 1.34/1.57  thf('53', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.34/1.57      inference('sup+', [status(thm)], ['39', '40'])).
% 1.34/1.57  thf('54', plain,
% 1.34/1.57      (![X19 : $i, X20 : $i]:
% 1.34/1.57         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 1.34/1.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.34/1.57  thf('55', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.34/1.57      inference('sup-', [status(thm)], ['53', '54'])).
% 1.34/1.57  thf('56', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.34/1.57      inference('demod', [status(thm)], ['14', '17'])).
% 1.34/1.57  thf('57', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.34/1.57      inference('sup+', [status(thm)], ['55', '56'])).
% 1.34/1.57  thf(t54_xboole_1, axiom,
% 1.34/1.57    (![A:$i,B:$i,C:$i]:
% 1.34/1.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 1.34/1.57       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.34/1.57  thf('58', plain,
% 1.34/1.57      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.34/1.57         ((k4_xboole_0 @ X30 @ (k3_xboole_0 @ X31 @ X32))
% 1.34/1.57           = (k2_xboole_0 @ (k4_xboole_0 @ X30 @ X31) @ 
% 1.34/1.57              (k4_xboole_0 @ X30 @ X32)))),
% 1.34/1.57      inference('cnf', [status(esa)], [t54_xboole_1])).
% 1.34/1.57  thf('59', plain,
% 1.34/1.57      (![X86 : $i, X87 : $i]:
% 1.34/1.57         ((k3_tarski @ (k2_tarski @ X86 @ X87)) = (k2_xboole_0 @ X86 @ X87))),
% 1.34/1.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.34/1.57  thf('60', plain,
% 1.34/1.57      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.34/1.57         ((k4_xboole_0 @ X30 @ (k3_xboole_0 @ X31 @ X32))
% 1.34/1.57           = (k3_tarski @ 
% 1.34/1.57              (k2_tarski @ (k4_xboole_0 @ X30 @ X31) @ 
% 1.34/1.57               (k4_xboole_0 @ X30 @ X32))))),
% 1.34/1.57      inference('demod', [status(thm)], ['58', '59'])).
% 1.34/1.57  thf('61', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.34/1.57           = (k3_tarski @ (k2_tarski @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)))),
% 1.34/1.57      inference('sup+', [status(thm)], ['57', '60'])).
% 1.34/1.57  thf(t1_boole, axiom,
% 1.34/1.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.34/1.57  thf('62', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 1.34/1.57      inference('cnf', [status(esa)], [t1_boole])).
% 1.34/1.57  thf('63', plain,
% 1.34/1.57      (![X86 : $i, X87 : $i]:
% 1.34/1.57         ((k3_tarski @ (k2_tarski @ X86 @ X87)) = (k2_xboole_0 @ X86 @ X87))),
% 1.34/1.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.34/1.57  thf('64', plain,
% 1.34/1.57      (![X16 : $i]: ((k3_tarski @ (k2_tarski @ X16 @ k1_xboole_0)) = (X16))),
% 1.34/1.57      inference('demod', [status(thm)], ['62', '63'])).
% 1.34/1.57  thf('65', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.34/1.57           = (k4_xboole_0 @ X0 @ X1))),
% 1.34/1.57      inference('demod', [status(thm)], ['61', '64'])).
% 1.34/1.57  thf('66', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]:
% 1.34/1.57         (((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0))
% 1.34/1.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.34/1.57      inference('demod', [status(thm)], ['52', '65'])).
% 1.34/1.57  thf('67', plain,
% 1.34/1.57      (((((k1_xboole_0) != (k1_xboole_0))
% 1.34/1.57         | ((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 1.34/1.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.34/1.57      inference('sup-', [status(thm)], ['49', '66'])).
% 1.34/1.57  thf('68', plain,
% 1.34/1.57      ((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 1.34/1.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.34/1.57      inference('simplify', [status(thm)], ['67'])).
% 1.34/1.57  thf('69', plain, (![X8 : $i]: ((k3_tarski @ (k2_tarski @ X8 @ X8)) = (X8))),
% 1.34/1.57      inference('demod', [status(thm)], ['9', '10'])).
% 1.34/1.57  thf(t29_xboole_1, axiom,
% 1.34/1.57    (![A:$i,B:$i,C:$i]:
% 1.34/1.57     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 1.34/1.57  thf('70', plain,
% 1.34/1.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.34/1.57         (r1_tarski @ (k3_xboole_0 @ X21 @ X22) @ (k2_xboole_0 @ X21 @ X23))),
% 1.34/1.57      inference('cnf', [status(esa)], [t29_xboole_1])).
% 1.34/1.57  thf('71', plain,
% 1.34/1.57      (![X86 : $i, X87 : $i]:
% 1.34/1.57         ((k3_tarski @ (k2_tarski @ X86 @ X87)) = (k2_xboole_0 @ X86 @ X87))),
% 1.34/1.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.34/1.57  thf('72', plain,
% 1.34/1.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.34/1.57         (r1_tarski @ (k3_xboole_0 @ X21 @ X22) @ 
% 1.34/1.57          (k3_tarski @ (k2_tarski @ X21 @ X23)))),
% 1.34/1.57      inference('demod', [status(thm)], ['70', '71'])).
% 1.34/1.57  thf('73', plain,
% 1.34/1.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.34/1.57      inference('sup+', [status(thm)], ['69', '72'])).
% 1.34/1.57  thf('74', plain,
% 1.34/1.57      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 1.34/1.57         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.34/1.57      inference('sup+', [status(thm)], ['68', '73'])).
% 1.34/1.57  thf('75', plain,
% 1.34/1.57      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 1.34/1.57         <= (~ ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.34/1.57      inference('split', [status(esa)], ['0'])).
% 1.34/1.57  thf('76', plain,
% 1.34/1.57      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.34/1.57       ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.34/1.57      inference('sup-', [status(thm)], ['74', '75'])).
% 1.34/1.57  thf('77', plain, ($false),
% 1.34/1.57      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '76'])).
% 1.34/1.57  
% 1.34/1.57  % SZS output end Refutation
% 1.34/1.57  
% 1.34/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
