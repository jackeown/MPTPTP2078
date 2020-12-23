%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xfP65fIrkR

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:29 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 121 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  580 ( 937 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_C_2 ) @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_C_2 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X35 ) @ X36 )
      | ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( r1_xboole_0 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['28','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['25','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('63',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xfP65fIrkR
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.15  % Solved by: fo/fo7.sh
% 0.91/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.15  % done 1503 iterations in 0.659s
% 0.91/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.15  % SZS output start Refutation
% 0.91/1.15  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.15  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.91/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.15  thf(sk_D_type, type, sk_D: $i).
% 0.91/1.15  thf(t149_zfmisc_1, conjecture,
% 0.91/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.15     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.91/1.15         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.91/1.15       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.91/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.15    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.15        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.91/1.15            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.91/1.15          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.91/1.15    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.91/1.15  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf(commutativity_k3_xboole_0, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.91/1.15  thf('1', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.15  thf(t48_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.91/1.15  thf('2', plain,
% 0.91/1.15      (![X16 : $i, X17 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.91/1.15           = (k3_xboole_0 @ X16 @ X17))),
% 0.91/1.15      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.15  thf(t36_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.91/1.15  thf('3', plain,
% 0.91/1.15      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.91/1.15      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.91/1.15  thf('4', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.91/1.15      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.15  thf('5', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.91/1.15      inference('sup+', [status(thm)], ['1', '4'])).
% 0.91/1.15  thf('6', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf(symmetry_r1_xboole_0, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.91/1.15  thf('7', plain,
% 0.91/1.15      (![X2 : $i, X3 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.91/1.15      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.91/1.15  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.91/1.15      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.15  thf(t3_xboole_0, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.91/1.15            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.15       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.15            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.91/1.15  thf('9', plain,
% 0.91/1.15      (![X4 : $i, X5 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.91/1.15      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.15  thf(t4_xboole_0, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.15            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.15       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.15            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.91/1.15  thf('10', plain,
% 0.91/1.15      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.91/1.15          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.91/1.15      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.91/1.15  thf('11', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.91/1.15          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('12', plain,
% 0.91/1.15      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_2) @ X0)),
% 0.91/1.15      inference('sup-', [status(thm)], ['8', '11'])).
% 0.91/1.15  thf('13', plain,
% 0.91/1.15      (![X2 : $i, X3 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.91/1.15      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.91/1.15  thf('14', plain,
% 0.91/1.15      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_C_2))),
% 0.91/1.15      inference('sup-', [status(thm)], ['12', '13'])).
% 0.91/1.15  thf('15', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.15  thf(t77_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.91/1.15          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.91/1.15  thf('16', plain,
% 0.91/1.15      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X26 @ X27)
% 0.91/1.15          | ~ (r1_xboole_0 @ X26 @ (k3_xboole_0 @ X27 @ X28))
% 0.91/1.15          | ~ (r1_tarski @ X26 @ X28))),
% 0.91/1.15      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.91/1.15  thf('17', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         (~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.15          | ~ (r1_tarski @ X2 @ X1)
% 0.91/1.15          | (r1_xboole_0 @ X2 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['15', '16'])).
% 0.91/1.15  thf('18', plain,
% 0.91/1.15      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_C_2) | ~ (r1_tarski @ X0 @ sk_B))),
% 0.91/1.15      inference('sup-', [status(thm)], ['14', '17'])).
% 0.91/1.15  thf('19', plain,
% 0.91/1.15      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_C_2)),
% 0.91/1.15      inference('sup-', [status(thm)], ['5', '18'])).
% 0.91/1.15  thf('20', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.91/1.15      inference('sup+', [status(thm)], ['2', '3'])).
% 0.91/1.15  thf(t73_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.91/1.15       ( r1_tarski @ A @ B ) ))).
% 0.91/1.15  thf('21', plain,
% 0.91/1.15      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.91/1.15         ((r1_tarski @ X18 @ X19)
% 0.91/1.15          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 0.91/1.15          | ~ (r1_xboole_0 @ X18 @ X20))),
% 0.91/1.15      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.91/1.15  thf('22', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         (~ (r1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X0)
% 0.91/1.15          | (r1_tarski @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.15  thf('23', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (r1_tarski @ (k3_xboole_0 @ (k2_xboole_0 @ X0 @ sk_C_2) @ sk_B) @ X0)),
% 0.91/1.15      inference('sup-', [status(thm)], ['19', '22'])).
% 0.91/1.15  thf('24', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.15  thf('25', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (r1_tarski @ (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_C_2)) @ X0)),
% 0.91/1.15      inference('demod', [status(thm)], ['23', '24'])).
% 0.91/1.15  thf('26', plain,
% 0.91/1.15      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('27', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.15  thf('28', plain,
% 0.91/1.15      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.91/1.15      inference('demod', [status(thm)], ['26', '27'])).
% 0.91/1.15  thf(l27_zfmisc_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.91/1.15  thf('29', plain,
% 0.91/1.15      (![X35 : $i, X36 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ (k1_tarski @ X35) @ X36) | (r2_hidden @ X35 @ X36))),
% 0.91/1.15      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.91/1.15  thf('30', plain,
% 0.91/1.15      (![X2 : $i, X3 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.91/1.15      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.91/1.15  thf('31', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.15  thf(t75_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.15          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.91/1.15  thf('32', plain,
% 0.91/1.15      (![X24 : $i, X25 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X24 @ X25)
% 0.91/1.15          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ X25))),
% 0.91/1.15      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.91/1.15  thf('33', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.91/1.15          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['31', '32'])).
% 0.91/1.15  thf('34', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf(t74_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.91/1.15          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.91/1.15  thf('35', plain,
% 0.91/1.15      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.91/1.15         (~ (r1_xboole_0 @ X21 @ X22)
% 0.91/1.15          | (r1_xboole_0 @ X21 @ (k3_xboole_0 @ X22 @ X23)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.91/1.15  thf('36', plain,
% 0.91/1.15      (![X0 : $i]: (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ sk_B @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.15  thf('37', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('38', plain,
% 0.91/1.15      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X6 @ X4)
% 0.91/1.15          | ~ (r2_hidden @ X6 @ X7)
% 0.91/1.15          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.91/1.15      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.15  thf('39', plain,
% 0.91/1.15      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.15  thf('40', plain,
% 0.91/1.15      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['36', '39'])).
% 0.91/1.15  thf('41', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 0.91/1.15      inference('sup-', [status(thm)], ['33', '40'])).
% 0.91/1.15  thf('42', plain,
% 0.91/1.15      (![X4 : $i, X5 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.91/1.15      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.15  thf('43', plain,
% 0.91/1.15      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.91/1.15          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.91/1.15      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.91/1.15  thf('44', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.15          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.15  thf('45', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['41', '44'])).
% 0.91/1.15  thf('46', plain,
% 0.91/1.15      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X26 @ X27)
% 0.91/1.15          | ~ (r1_xboole_0 @ X26 @ (k3_xboole_0 @ X27 @ X28))
% 0.91/1.15          | ~ (r1_tarski @ X26 @ X28))),
% 0.91/1.15      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.91/1.15  thf('47', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 0.91/1.15      inference('sup-', [status(thm)], ['45', '46'])).
% 0.91/1.15  thf('48', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 0.91/1.15      inference('sup-', [status(thm)], ['28', '47'])).
% 0.91/1.15  thf('49', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.15  thf('50', plain,
% 0.91/1.15      (![X24 : $i, X25 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X24 @ X25)
% 0.91/1.15          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ X25))),
% 0.91/1.15      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.91/1.15  thf('51', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.91/1.15          | (r1_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.15  thf('52', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.91/1.15      inference('sup-', [status(thm)], ['48', '51'])).
% 0.91/1.15  thf('53', plain,
% 0.91/1.15      (![X4 : $i, X5 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.91/1.15      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.15  thf('54', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.15  thf('55', plain,
% 0.91/1.15      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.91/1.15          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.91/1.15      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.91/1.15  thf('56', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.15          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['54', '55'])).
% 0.91/1.15  thf('57', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.15          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['53', '56'])).
% 0.91/1.15  thf('58', plain,
% 0.91/1.15      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.91/1.15      inference('sup-', [status(thm)], ['52', '57'])).
% 0.91/1.15  thf('59', plain,
% 0.91/1.15      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.91/1.15         ((r1_xboole_0 @ X26 @ X27)
% 0.91/1.15          | ~ (r1_xboole_0 @ X26 @ (k3_xboole_0 @ X27 @ X28))
% 0.91/1.15          | ~ (r1_tarski @ X26 @ X28))),
% 0.91/1.15      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.91/1.15  thf('60', plain,
% 0.91/1.15      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_A) | (r1_xboole_0 @ X0 @ sk_B))),
% 0.91/1.15      inference('sup-', [status(thm)], ['58', '59'])).
% 0.91/1.15  thf('61', plain,
% 0.91/1.15      ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2)) @ 
% 0.91/1.15        sk_B)),
% 0.91/1.15      inference('sup-', [status(thm)], ['25', '60'])).
% 0.91/1.15  thf('62', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.91/1.15          | (r1_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.15  thf('63', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.91/1.15      inference('sup-', [status(thm)], ['61', '62'])).
% 0.91/1.15  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.91/1.15  
% 0.91/1.15  % SZS output end Refutation
% 0.91/1.15  
% 0.91/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
