%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A1BxoM3C6B

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:08 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 216 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   20
%              Number of atoms          :  734 (2028 expanded)
%              Number of equality atoms :   41 ( 123 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) ) )
      | ( r2_hidden @ X19 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X14 @ X11 ) @ ( sk_D @ X14 @ X11 ) ) @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) ) )
      | ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('29',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('37',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','44'])).

thf('46',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','45'])).

thf('47',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('48',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('49',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','44','48'])).

thf('50',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X21 ) )
      | ( r2_hidden @ X19 @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('62',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['46','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A1BxoM3C6B
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.61/1.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.61/1.89  % Solved by: fo/fo7.sh
% 1.61/1.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.89  % done 1634 iterations in 1.428s
% 1.61/1.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.61/1.89  % SZS output start Refutation
% 1.61/1.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.61/1.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.61/1.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.61/1.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.61/1.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.61/1.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.61/1.89  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.89  thf(sk_B_type, type, sk_B: $i).
% 1.61/1.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.61/1.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.61/1.89  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.61/1.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.61/1.89  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.61/1.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.61/1.89  thf(t95_relat_1, conjecture,
% 1.61/1.89    (![A:$i,B:$i]:
% 1.61/1.89     ( ( v1_relat_1 @ B ) =>
% 1.61/1.89       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 1.61/1.89         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.61/1.89  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.89    (~( ![A:$i,B:$i]:
% 1.61/1.89        ( ( v1_relat_1 @ B ) =>
% 1.61/1.89          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 1.61/1.89            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 1.61/1.89    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 1.61/1.89  thf('0', plain,
% 1.61/1.89      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.61/1.89        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 1.61/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.89  thf('1', plain,
% 1.61/1.89      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.61/1.89         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('split', [status(esa)], ['0'])).
% 1.61/1.89  thf('2', plain,
% 1.61/1.89      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 1.61/1.89       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.61/1.89      inference('split', [status(esa)], ['0'])).
% 1.61/1.89  thf(dt_k7_relat_1, axiom,
% 1.61/1.89    (![A:$i,B:$i]:
% 1.61/1.89     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.61/1.89  thf('3', plain,
% 1.61/1.89      (![X16 : $i, X17 : $i]:
% 1.61/1.89         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 1.61/1.89      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.61/1.89  thf('4', plain,
% 1.61/1.89      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.61/1.89        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.61/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.89  thf('5', plain,
% 1.61/1.89      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.61/1.89         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('split', [status(esa)], ['4'])).
% 1.61/1.89  thf(symmetry_r1_xboole_0, axiom,
% 1.61/1.89    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.61/1.89  thf('6', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.61/1.89      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.61/1.89  thf('7', plain,
% 1.61/1.89      (((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.61/1.89         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('sup-', [status(thm)], ['5', '6'])).
% 1.61/1.89  thf(t3_xboole_0, axiom,
% 1.61/1.89    (![A:$i,B:$i]:
% 1.61/1.89     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.61/1.89            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.61/1.89       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.61/1.89            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.61/1.89  thf('8', plain,
% 1.61/1.89      (![X2 : $i, X3 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 1.61/1.89      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.61/1.89  thf(t86_relat_1, axiom,
% 1.61/1.89    (![A:$i,B:$i,C:$i]:
% 1.61/1.89     ( ( v1_relat_1 @ C ) =>
% 1.61/1.89       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 1.61/1.89         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 1.61/1.89  thf('9', plain,
% 1.61/1.89      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.61/1.89         (~ (r2_hidden @ X19 @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X20)))
% 1.61/1.89          | (r2_hidden @ X19 @ (k1_relat_1 @ X21))
% 1.61/1.89          | ~ (v1_relat_1 @ X21))),
% 1.61/1.89      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.61/1.89  thf('10', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 1.61/1.89          | ~ (v1_relat_1 @ X1)
% 1.61/1.89          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 1.61/1.89             (k1_relat_1 @ X1)))),
% 1.61/1.89      inference('sup-', [status(thm)], ['8', '9'])).
% 1.61/1.89  thf('11', plain,
% 1.61/1.89      (![X2 : $i, X3 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 1.61/1.89      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.61/1.89  thf('12', plain,
% 1.61/1.89      (![X2 : $i, X4 : $i, X5 : $i]:
% 1.61/1.89         (~ (r2_hidden @ X4 @ X2)
% 1.61/1.89          | ~ (r2_hidden @ X4 @ X5)
% 1.61/1.89          | ~ (r1_xboole_0 @ X2 @ X5))),
% 1.61/1.89      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.61/1.89  thf('13', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ X1 @ X0)
% 1.61/1.89          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.61/1.89          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.61/1.89      inference('sup-', [status(thm)], ['11', '12'])).
% 1.61/1.89  thf('14', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.89         (~ (v1_relat_1 @ X0)
% 1.61/1.89          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 1.61/1.89          | ~ (r1_xboole_0 @ X2 @ (k1_relat_1 @ X0))
% 1.61/1.89          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2))),
% 1.61/1.89      inference('sup-', [status(thm)], ['10', '13'])).
% 1.61/1.89  thf('15', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.89         (~ (r1_xboole_0 @ X2 @ (k1_relat_1 @ X0))
% 1.61/1.89          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 1.61/1.89          | ~ (v1_relat_1 @ X0))),
% 1.61/1.89      inference('simplify', [status(thm)], ['14'])).
% 1.61/1.89  thf('16', plain,
% 1.61/1.89      ((![X0 : $i]:
% 1.61/1.89          (~ (v1_relat_1 @ sk_B)
% 1.61/1.89           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A)))
% 1.61/1.89         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('sup-', [status(thm)], ['7', '15'])).
% 1.61/1.89  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.89  thf('18', plain,
% 1.61/1.89      ((![X0 : $i]:
% 1.61/1.89          (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A))
% 1.61/1.89         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('demod', [status(thm)], ['16', '17'])).
% 1.61/1.89  thf(d4_relat_1, axiom,
% 1.61/1.89    (![A:$i,B:$i]:
% 1.61/1.89     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.61/1.89       ( ![C:$i]:
% 1.61/1.89         ( ( r2_hidden @ C @ B ) <=>
% 1.61/1.89           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.61/1.89  thf('19', plain,
% 1.61/1.89      (![X11 : $i, X14 : $i]:
% 1.61/1.89         (((X14) = (k1_relat_1 @ X11))
% 1.61/1.89          | (r2_hidden @ 
% 1.61/1.89             (k4_tarski @ (sk_C_1 @ X14 @ X11) @ (sk_D @ X14 @ X11)) @ X11)
% 1.61/1.89          | (r2_hidden @ (sk_C_1 @ X14 @ X11) @ X14))),
% 1.61/1.89      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.61/1.89  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.61/1.89  thf('20', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 1.61/1.89      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.61/1.89  thf(l24_zfmisc_1, axiom,
% 1.61/1.89    (![A:$i,B:$i]:
% 1.61/1.89     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 1.61/1.89  thf('21', plain,
% 1.61/1.89      (![X7 : $i, X8 : $i]:
% 1.61/1.89         (~ (r1_xboole_0 @ (k1_tarski @ X7) @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 1.61/1.89      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 1.61/1.89  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.61/1.89      inference('sup-', [status(thm)], ['20', '21'])).
% 1.61/1.89  thf('23', plain,
% 1.61/1.89      (![X0 : $i]:
% 1.61/1.89         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 1.61/1.89          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 1.61/1.89      inference('sup-', [status(thm)], ['19', '22'])).
% 1.61/1.89  thf(t60_relat_1, axiom,
% 1.61/1.89    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.61/1.89     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.61/1.89  thf('24', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.61/1.89  thf('25', plain,
% 1.61/1.89      (![X0 : $i]:
% 1.61/1.89         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 1.61/1.89          | ((X0) = (k1_xboole_0)))),
% 1.61/1.89      inference('demod', [status(thm)], ['23', '24'])).
% 1.61/1.89  thf('26', plain,
% 1.61/1.89      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.61/1.89         (~ (r2_hidden @ X19 @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X20)))
% 1.61/1.89          | (r2_hidden @ X19 @ X20)
% 1.61/1.89          | ~ (v1_relat_1 @ X21))),
% 1.61/1.89      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.61/1.89  thf('27', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i]:
% 1.61/1.89         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0))
% 1.61/1.89          | ~ (v1_relat_1 @ X1)
% 1.61/1.89          | (r2_hidden @ 
% 1.61/1.89             (sk_C_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ k1_xboole_0) @ 
% 1.61/1.89             X0))),
% 1.61/1.89      inference('sup-', [status(thm)], ['25', '26'])).
% 1.61/1.89  thf('28', plain,
% 1.61/1.89      (![X0 : $i]:
% 1.61/1.89         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 1.61/1.89          | ((X0) = (k1_xboole_0)))),
% 1.61/1.89      inference('demod', [status(thm)], ['23', '24'])).
% 1.61/1.89  thf('29', plain,
% 1.61/1.89      (![X2 : $i, X4 : $i, X5 : $i]:
% 1.61/1.89         (~ (r2_hidden @ X4 @ X2)
% 1.61/1.89          | ~ (r2_hidden @ X4 @ X5)
% 1.61/1.89          | ~ (r1_xboole_0 @ X2 @ X5))),
% 1.61/1.89      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.61/1.89  thf('30', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i]:
% 1.61/1.89         (((X0) = (k1_xboole_0))
% 1.61/1.89          | ~ (r1_xboole_0 @ X0 @ X1)
% 1.61/1.89          | ~ (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1))),
% 1.61/1.89      inference('sup-', [status(thm)], ['28', '29'])).
% 1.61/1.89  thf('31', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i]:
% 1.61/1.89         (~ (v1_relat_1 @ X1)
% 1.61/1.89          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0))
% 1.61/1.89          | ~ (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 1.61/1.89          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0)))),
% 1.61/1.89      inference('sup-', [status(thm)], ['27', '30'])).
% 1.61/1.89  thf('32', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i]:
% 1.61/1.89         (~ (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 1.61/1.89          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0))
% 1.61/1.89          | ~ (v1_relat_1 @ X1))),
% 1.61/1.89      inference('simplify', [status(thm)], ['31'])).
% 1.61/1.89  thf('33', plain,
% 1.61/1.89      (((~ (v1_relat_1 @ sk_B)
% 1.61/1.89         | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 1.61/1.89         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('sup-', [status(thm)], ['18', '32'])).
% 1.61/1.89  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.89  thf('35', plain,
% 1.61/1.89      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0)))
% 1.61/1.89         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('demod', [status(thm)], ['33', '34'])).
% 1.61/1.89  thf(t64_relat_1, axiom,
% 1.61/1.89    (![A:$i]:
% 1.61/1.89     ( ( v1_relat_1 @ A ) =>
% 1.61/1.89       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.61/1.89           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.61/1.89         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.61/1.89  thf('36', plain,
% 1.61/1.89      (![X18 : $i]:
% 1.61/1.89         (((k1_relat_1 @ X18) != (k1_xboole_0))
% 1.61/1.89          | ((X18) = (k1_xboole_0))
% 1.61/1.89          | ~ (v1_relat_1 @ X18))),
% 1.61/1.89      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.61/1.89  thf('37', plain,
% 1.61/1.89      (((((k1_xboole_0) != (k1_xboole_0))
% 1.61/1.89         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 1.61/1.89         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 1.61/1.89         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('sup-', [status(thm)], ['35', '36'])).
% 1.61/1.89  thf('38', plain,
% 1.61/1.89      (((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.61/1.89         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 1.61/1.89         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('simplify', [status(thm)], ['37'])).
% 1.61/1.89  thf('39', plain,
% 1.61/1.89      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 1.61/1.89         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('sup-', [status(thm)], ['3', '38'])).
% 1.61/1.89  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.89  thf('41', plain,
% 1.61/1.89      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 1.61/1.89         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('demod', [status(thm)], ['39', '40'])).
% 1.61/1.89  thf('42', plain,
% 1.61/1.89      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 1.61/1.89         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 1.61/1.89      inference('split', [status(esa)], ['0'])).
% 1.61/1.89  thf('43', plain,
% 1.61/1.89      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.61/1.89         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 1.61/1.89             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.61/1.89      inference('sup-', [status(thm)], ['41', '42'])).
% 1.61/1.89  thf('44', plain,
% 1.61/1.89      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 1.61/1.89       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.61/1.89      inference('simplify', [status(thm)], ['43'])).
% 1.61/1.89  thf('45', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.61/1.89      inference('sat_resolution*', [status(thm)], ['2', '44'])).
% 1.61/1.89  thf('46', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 1.61/1.89      inference('simpl_trail', [status(thm)], ['1', '45'])).
% 1.61/1.89  thf('47', plain,
% 1.61/1.89      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 1.61/1.89         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 1.61/1.89      inference('split', [status(esa)], ['4'])).
% 1.61/1.89  thf('48', plain,
% 1.61/1.89      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 1.61/1.89       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.61/1.89      inference('split', [status(esa)], ['4'])).
% 1.61/1.89  thf('49', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.61/1.89      inference('sat_resolution*', [status(thm)], ['2', '44', '48'])).
% 1.61/1.89  thf('50', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.61/1.89      inference('simpl_trail', [status(thm)], ['47', '49'])).
% 1.61/1.89  thf('51', plain,
% 1.61/1.89      (![X2 : $i, X3 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 1.61/1.89      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.61/1.89  thf('52', plain,
% 1.61/1.89      (![X2 : $i, X3 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 1.61/1.89      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.61/1.89  thf('53', plain,
% 1.61/1.89      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.61/1.89         (~ (r2_hidden @ X19 @ X20)
% 1.61/1.89          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X21))
% 1.61/1.89          | (r2_hidden @ X19 @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X20)))
% 1.61/1.89          | ~ (v1_relat_1 @ X21))),
% 1.61/1.89      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.61/1.89  thf('54', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 1.61/1.89          | ~ (v1_relat_1 @ X0)
% 1.61/1.89          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 1.61/1.89             (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 1.61/1.89          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 1.61/1.89      inference('sup-', [status(thm)], ['52', '53'])).
% 1.61/1.89  thf('55', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 1.61/1.89          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 1.61/1.89             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.61/1.89          | ~ (v1_relat_1 @ X1)
% 1.61/1.89          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 1.61/1.89      inference('sup-', [status(thm)], ['51', '54'])).
% 1.61/1.89  thf('56', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i]:
% 1.61/1.89         (~ (v1_relat_1 @ X1)
% 1.61/1.89          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 1.61/1.89             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.61/1.89          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 1.61/1.89      inference('simplify', [status(thm)], ['55'])).
% 1.61/1.89  thf('57', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ X1 @ X0)
% 1.61/1.89          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.61/1.89          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.61/1.89      inference('sup-', [status(thm)], ['11', '12'])).
% 1.61/1.89  thf('58', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i]:
% 1.61/1.89         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 1.61/1.89          | ~ (v1_relat_1 @ X1)
% 1.61/1.89          | ~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.61/1.89          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 1.61/1.89      inference('sup-', [status(thm)], ['56', '57'])).
% 1.61/1.89  thf('59', plain,
% 1.61/1.89      (![X0 : $i, X1 : $i]:
% 1.61/1.89         (~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.61/1.89          | ~ (v1_relat_1 @ X1)
% 1.61/1.89          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 1.61/1.89      inference('simplify', [status(thm)], ['58'])).
% 1.61/1.89  thf('60', plain,
% 1.61/1.89      ((~ (r1_xboole_0 @ sk_A @ (k1_relat_1 @ k1_xboole_0))
% 1.61/1.89        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.61/1.89        | ~ (v1_relat_1 @ sk_B))),
% 1.61/1.89      inference('sup-', [status(thm)], ['50', '59'])).
% 1.61/1.89  thf('61', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.61/1.89      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.61/1.89  thf('62', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 1.61/1.89      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.61/1.89  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 1.61/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.89  thf('64', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 1.61/1.89      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 1.61/1.89  thf('65', plain, ($false), inference('demod', [status(thm)], ['46', '64'])).
% 1.61/1.89  
% 1.61/1.89  % SZS output end Refutation
% 1.61/1.89  
% 1.61/1.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
