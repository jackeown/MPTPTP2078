%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OJ2FXahFqQ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:15 EST 2020

% Result     : Theorem 9.63s
% Output     : Refutation 9.63s
% Verified   : 
% Statistics : Number of formulae       :   71 (  95 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   18
%              Number of atoms          :  618 ( 957 expanded)
%              Number of equality atoms :   32 (  46 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t127_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ B )
          | ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t127_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['1'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_D )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t122_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ X25 @ ( k3_xboole_0 @ X22 @ X24 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X25 @ X22 ) @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
         != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X17 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ sk_C ) @ ( k2_zfmisc_1 @ X1 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X22 @ X24 ) @ X23 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_zfmisc_1 @ X16 @ X17 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('25',plain,(
    ! [X17: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ ( k2_xboole_0 @ X18 @ X20 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X18 ) @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_B @ X1 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('33',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ X0 @ X1 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ ( k2_xboole_0 @ X18 @ X20 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X18 ) @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('35',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X8 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ X1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ X1 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('43',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ sk_C ) @ ( k2_zfmisc_1 @ X1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['16','43'])).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('48',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X8 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ( r1_xboole_0 @ X3 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ X1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OJ2FXahFqQ
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.63/9.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.63/9.83  % Solved by: fo/fo7.sh
% 9.63/9.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.63/9.83  % done 8611 iterations in 9.373s
% 9.63/9.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.63/9.83  % SZS output start Refutation
% 9.63/9.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.63/9.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.63/9.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.63/9.83  thf(sk_A_type, type, sk_A: $i).
% 9.63/9.83  thf(sk_C_type, type, sk_C: $i).
% 9.63/9.83  thf(sk_D_type, type, sk_D: $i).
% 9.63/9.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.63/9.83  thf(sk_B_type, type, sk_B: $i).
% 9.63/9.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.63/9.83  thf(t127_zfmisc_1, conjecture,
% 9.63/9.83    (![A:$i,B:$i,C:$i,D:$i]:
% 9.63/9.83     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 9.63/9.83       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 9.63/9.83  thf(zf_stmt_0, negated_conjecture,
% 9.63/9.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 9.63/9.83        ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 9.63/9.83          ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 9.63/9.83    inference('cnf.neg', [status(esa)], [t127_zfmisc_1])).
% 9.63/9.83  thf('0', plain,
% 9.63/9.83      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 9.63/9.83          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 9.63/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.63/9.83  thf('1', plain,
% 9.63/9.83      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_C @ sk_D))),
% 9.63/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.63/9.83  thf('2', plain,
% 9.63/9.83      (((r1_xboole_0 @ sk_C @ sk_D)) <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 9.63/9.83      inference('split', [status(esa)], ['1'])).
% 9.63/9.83  thf(d7_xboole_0, axiom,
% 9.63/9.83    (![A:$i,B:$i]:
% 9.63/9.83     ( ( r1_xboole_0 @ A @ B ) <=>
% 9.63/9.83       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 9.63/9.83  thf('3', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i]:
% 9.63/9.83         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 9.63/9.83      inference('cnf', [status(esa)], [d7_xboole_0])).
% 9.63/9.83  thf('4', plain,
% 9.63/9.83      ((((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0)))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['2', '3'])).
% 9.63/9.83  thf(t122_zfmisc_1, axiom,
% 9.63/9.83    (![A:$i,B:$i,C:$i]:
% 9.63/9.83     ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 9.63/9.83         ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 9.63/9.83       ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 9.63/9.83         ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 9.63/9.83  thf('5', plain,
% 9.63/9.83      (![X22 : $i, X24 : $i, X25 : $i]:
% 9.63/9.83         ((k2_zfmisc_1 @ X25 @ (k3_xboole_0 @ X22 @ X24))
% 9.63/9.83           = (k3_xboole_0 @ (k2_zfmisc_1 @ X25 @ X22) @ 
% 9.63/9.83              (k2_zfmisc_1 @ X25 @ X24)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 9.63/9.83  thf('6', plain,
% 9.63/9.83      (![X0 : $i, X2 : $i]:
% 9.63/9.83         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 9.63/9.83      inference('cnf', [status(esa)], [d7_xboole_0])).
% 9.63/9.83  thf('7', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.63/9.83         (((k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 9.63/9.83          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['5', '6'])).
% 9.63/9.83  thf('8', plain,
% 9.63/9.83      ((![X0 : $i]:
% 9.63/9.83          (((k2_zfmisc_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 9.63/9.83           | (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_C) @ 
% 9.63/9.83              (k2_zfmisc_1 @ X0 @ sk_D))))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['4', '7'])).
% 9.63/9.83  thf(t113_zfmisc_1, axiom,
% 9.63/9.83    (![A:$i,B:$i]:
% 9.63/9.83     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 9.63/9.83       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 9.63/9.83  thf('9', plain,
% 9.63/9.83      (![X16 : $i, X17 : $i]:
% 9.63/9.83         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 9.63/9.83          | ((X17) != (k1_xboole_0)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.63/9.83  thf('10', plain,
% 9.63/9.83      (![X16 : $i]: ((k2_zfmisc_1 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 9.63/9.83      inference('simplify', [status(thm)], ['9'])).
% 9.63/9.83  thf('11', plain,
% 9.63/9.83      ((![X0 : $i]:
% 9.63/9.83          (((k1_xboole_0) != (k1_xboole_0))
% 9.63/9.83           | (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_C) @ 
% 9.63/9.83              (k2_zfmisc_1 @ X0 @ sk_D))))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 9.63/9.83      inference('demod', [status(thm)], ['8', '10'])).
% 9.63/9.83  thf('12', plain,
% 9.63/9.83      ((![X0 : $i]:
% 9.63/9.83          (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_D)))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 9.63/9.83      inference('simplify', [status(thm)], ['11'])).
% 9.63/9.83  thf(t120_zfmisc_1, axiom,
% 9.63/9.83    (![A:$i,B:$i,C:$i]:
% 9.63/9.83     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 9.63/9.83         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 9.63/9.83       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 9.63/9.83         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 9.63/9.83  thf('13', plain,
% 9.63/9.83      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.63/9.83         ((k2_zfmisc_1 @ (k2_xboole_0 @ X18 @ X20) @ X19)
% 9.63/9.83           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 9.63/9.83              (k2_zfmisc_1 @ X20 @ X19)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.63/9.83  thf(t70_xboole_1, axiom,
% 9.63/9.83    (![A:$i,B:$i,C:$i]:
% 9.63/9.83     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 9.63/9.83            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 9.63/9.83       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 9.63/9.83            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 9.63/9.83  thf('14', plain,
% 9.63/9.83      (![X8 : $i, X9 : $i, X11 : $i]:
% 9.63/9.83         ((r1_xboole_0 @ X8 @ X9)
% 9.63/9.83          | ~ (r1_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X11)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t70_xboole_1])).
% 9.63/9.83  thf('15', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.63/9.83         (~ (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 9.63/9.83          | (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ X2 @ X0)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['13', '14'])).
% 9.63/9.83  thf('16', plain,
% 9.63/9.83      ((![X0 : $i, X1 : $i]:
% 9.63/9.83          (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0) @ sk_C) @ 
% 9.63/9.83           (k2_zfmisc_1 @ X1 @ sk_D)))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['12', '15'])).
% 9.63/9.83  thf('17', plain,
% 9.63/9.83      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 9.63/9.83      inference('split', [status(esa)], ['1'])).
% 9.63/9.83  thf('18', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i]:
% 9.63/9.83         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 9.63/9.83      inference('cnf', [status(esa)], [d7_xboole_0])).
% 9.63/9.83  thf('19', plain,
% 9.63/9.83      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['17', '18'])).
% 9.63/9.83  thf('20', plain,
% 9.63/9.83      (![X22 : $i, X23 : $i, X24 : $i]:
% 9.63/9.83         ((k2_zfmisc_1 @ (k3_xboole_0 @ X22 @ X24) @ X23)
% 9.63/9.83           = (k3_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 9.63/9.83              (k2_zfmisc_1 @ X24 @ X23)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 9.63/9.83  thf('21', plain,
% 9.63/9.83      (![X0 : $i, X2 : $i]:
% 9.63/9.83         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 9.63/9.83      inference('cnf', [status(esa)], [d7_xboole_0])).
% 9.63/9.83  thf('22', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.63/9.83         (((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 9.63/9.83          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['20', '21'])).
% 9.63/9.83  thf('23', plain,
% 9.63/9.83      ((![X0 : $i]:
% 9.63/9.83          (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 9.63/9.83           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 9.63/9.83              (k2_zfmisc_1 @ sk_B @ X0))))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['19', '22'])).
% 9.63/9.83  thf('24', plain,
% 9.63/9.83      (![X16 : $i, X17 : $i]:
% 9.63/9.83         (((k2_zfmisc_1 @ X16 @ X17) = (k1_xboole_0))
% 9.63/9.83          | ((X16) != (k1_xboole_0)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.63/9.83  thf('25', plain,
% 9.63/9.83      (![X17 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 9.63/9.83      inference('simplify', [status(thm)], ['24'])).
% 9.63/9.83  thf('26', plain,
% 9.63/9.83      ((![X0 : $i]:
% 9.63/9.83          (((k1_xboole_0) != (k1_xboole_0))
% 9.63/9.83           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 9.63/9.83              (k2_zfmisc_1 @ sk_B @ X0))))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 9.63/9.83      inference('demod', [status(thm)], ['23', '25'])).
% 9.63/9.83  thf('27', plain,
% 9.63/9.83      ((![X0 : $i]:
% 9.63/9.83          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ (k2_zfmisc_1 @ sk_B @ X0)))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 9.63/9.83      inference('simplify', [status(thm)], ['26'])).
% 9.63/9.83  thf('28', plain,
% 9.63/9.83      (![X18 : $i, X20 : $i, X21 : $i]:
% 9.63/9.83         ((k2_zfmisc_1 @ X21 @ (k2_xboole_0 @ X18 @ X20))
% 9.63/9.83           = (k2_xboole_0 @ (k2_zfmisc_1 @ X21 @ X18) @ 
% 9.63/9.83              (k2_zfmisc_1 @ X21 @ X20)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.63/9.83  thf('29', plain,
% 9.63/9.83      (![X8 : $i, X9 : $i, X11 : $i]:
% 9.63/9.83         ((r1_xboole_0 @ X8 @ X9)
% 9.63/9.83          | ~ (r1_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X11)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t70_xboole_1])).
% 9.63/9.83  thf('30', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.63/9.83         (~ (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 9.63/9.83          | (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['28', '29'])).
% 9.63/9.83  thf('31', plain,
% 9.63/9.83      ((![X0 : $i, X1 : $i]:
% 9.63/9.83          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ X1 @ X0)) @ 
% 9.63/9.83           (k2_zfmisc_1 @ sk_B @ X1)))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['27', '30'])).
% 9.63/9.83  thf(symmetry_r1_xboole_0, axiom,
% 9.63/9.83    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 9.63/9.83  thf('32', plain,
% 9.63/9.83      (![X3 : $i, X4 : $i]:
% 9.63/9.83         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 9.63/9.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 9.63/9.83  thf('33', plain,
% 9.63/9.83      ((![X0 : $i, X1 : $i]:
% 9.63/9.83          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ X0) @ 
% 9.63/9.83           (k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ X0 @ X1))))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['31', '32'])).
% 9.63/9.83  thf('34', plain,
% 9.63/9.83      (![X18 : $i, X20 : $i, X21 : $i]:
% 9.63/9.83         ((k2_zfmisc_1 @ X21 @ (k2_xboole_0 @ X18 @ X20))
% 9.63/9.83           = (k2_xboole_0 @ (k2_zfmisc_1 @ X21 @ X18) @ 
% 9.63/9.83              (k2_zfmisc_1 @ X21 @ X20)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.63/9.83  thf('35', plain,
% 9.63/9.83      (![X8 : $i, X9 : $i, X11 : $i]:
% 9.63/9.83         ((r1_xboole_0 @ X8 @ X11)
% 9.63/9.83          | ~ (r1_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X11)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t70_xboole_1])).
% 9.63/9.83  thf('36', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.63/9.83         (~ (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 9.63/9.83          | (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ X2 @ X0)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['34', '35'])).
% 9.63/9.83  thf('37', plain,
% 9.63/9.83      ((![X0 : $i, X1 : $i]:
% 9.63/9.83          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ X1) @ (k2_zfmisc_1 @ sk_A @ X0)))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['33', '36'])).
% 9.63/9.83  thf('38', plain,
% 9.63/9.83      (![X3 : $i, X4 : $i]:
% 9.63/9.83         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 9.63/9.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 9.63/9.83  thf('39', plain,
% 9.63/9.83      ((![X0 : $i, X1 : $i]:
% 9.63/9.83          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0) @ (k2_zfmisc_1 @ sk_B @ X1)))
% 9.63/9.83         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['37', '38'])).
% 9.63/9.83  thf('40', plain,
% 9.63/9.83      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 9.63/9.83          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 9.63/9.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.63/9.83  thf('41', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 9.63/9.83      inference('sup-', [status(thm)], ['39', '40'])).
% 9.63/9.83  thf('42', plain,
% 9.63/9.83      (((r1_xboole_0 @ sk_C @ sk_D)) | ((r1_xboole_0 @ sk_A @ sk_B))),
% 9.63/9.83      inference('split', [status(esa)], ['1'])).
% 9.63/9.83  thf('43', plain, (((r1_xboole_0 @ sk_C @ sk_D))),
% 9.63/9.83      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 9.63/9.83  thf('44', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i]:
% 9.63/9.83         (r1_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0) @ sk_C) @ 
% 9.63/9.83          (k2_zfmisc_1 @ X1 @ sk_D))),
% 9.63/9.83      inference('simpl_trail', [status(thm)], ['16', '43'])).
% 9.63/9.83  thf('45', plain,
% 9.63/9.83      (![X3 : $i, X4 : $i]:
% 9.63/9.83         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 9.63/9.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 9.63/9.83  thf('46', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i]:
% 9.63/9.83         (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_D) @ 
% 9.63/9.83          (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ X1) @ sk_C))),
% 9.63/9.83      inference('sup-', [status(thm)], ['44', '45'])).
% 9.63/9.83  thf('47', plain,
% 9.63/9.83      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.63/9.83         ((k2_zfmisc_1 @ (k2_xboole_0 @ X18 @ X20) @ X19)
% 9.63/9.83           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 9.63/9.83              (k2_zfmisc_1 @ X20 @ X19)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 9.63/9.83  thf('48', plain,
% 9.63/9.83      (![X8 : $i, X9 : $i, X11 : $i]:
% 9.63/9.83         ((r1_xboole_0 @ X8 @ X11)
% 9.63/9.83          | ~ (r1_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X11)))),
% 9.63/9.83      inference('cnf', [status(esa)], [t70_xboole_1])).
% 9.63/9.83  thf('49', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.63/9.83         (~ (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 9.63/9.83          | (r1_xboole_0 @ X3 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 9.63/9.83      inference('sup-', [status(thm)], ['47', '48'])).
% 9.63/9.83  thf('50', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i]:
% 9.63/9.83         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_D) @ (k2_zfmisc_1 @ X0 @ sk_C))),
% 9.63/9.83      inference('sup-', [status(thm)], ['46', '49'])).
% 9.63/9.83  thf('51', plain,
% 9.63/9.83      (![X3 : $i, X4 : $i]:
% 9.63/9.83         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 9.63/9.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 9.63/9.83  thf('52', plain,
% 9.63/9.83      (![X0 : $i, X1 : $i]:
% 9.63/9.83         (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_C) @ (k2_zfmisc_1 @ X1 @ sk_D))),
% 9.63/9.83      inference('sup-', [status(thm)], ['50', '51'])).
% 9.63/9.83  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 9.63/9.83  
% 9.63/9.83  % SZS output end Refutation
% 9.63/9.83  
% 9.63/9.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
