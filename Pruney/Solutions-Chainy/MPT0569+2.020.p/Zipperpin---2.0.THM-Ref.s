%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0p7VsB3RPo

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:05 EST 2020

% Result     : Theorem 6.28s
% Output     : Refutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 187 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :   19
%              Number of atoms          :  678 (1777 expanded)
%              Number of equality atoms :   40 ( 128 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
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
    ( ( r1_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22
        = ( k2_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X22 @ X19 ) @ ( sk_C_1 @ X22 @ X19 ) ) @ X19 )
      | ( r2_hidden @ ( sk_C_1 @ X22 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ~ ( r2_hidden @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k10_relat_1 @ X27 @ X25 ) )
      | ( r2_hidden @ ( sk_D_3 @ X27 @ X25 @ X26 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_3 @ X1 @ X0 @ ( sk_C_1 @ ( k10_relat_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k10_relat_1 @ X27 @ X25 ) )
      | ( r2_hidden @ ( sk_D_3 @ X27 @ X25 @ X26 ) @ X25 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_3 @ X1 @ X0 @ ( sk_C_1 @ ( k10_relat_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D_3 @ X1 @ X0 @ ( sk_C_1 @ ( k10_relat_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k10_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','34'])).

thf('36',plain,(
    ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('37',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,
    ( ( ( k10_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','34','38'])).

thf('40',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X21 @ X19 ) @ X21 ) @ X19 )
      | ( X20
       != ( k2_relat_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('44',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X21 @ X19 ) @ X21 ) @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i,X13: $i,X15: $i,X16: $i] :
      ( ( X13
       != ( k10_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X11 )
      | ~ ( r2_hidden @ X16 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('47',plain,(
    ! [X10: $i,X11: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X16 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X11 )
      | ( r2_hidden @ X15 @ ( k10_relat_1 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X0 @ ( k2_relat_1 @ X1 ) ) @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X0 @ ( k2_relat_1 @ X1 ) ) @ X1 ) @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_D_2 @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_D_2 @ ( sk_C @ sk_A @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('55',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['36','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0p7VsB3RPo
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:40:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.28/6.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.28/6.48  % Solved by: fo/fo7.sh
% 6.28/6.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.28/6.48  % done 2558 iterations in 6.017s
% 6.28/6.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.28/6.48  % SZS output start Refutation
% 6.28/6.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.28/6.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.28/6.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.28/6.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.28/6.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 6.28/6.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.28/6.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.28/6.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.28/6.48  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 6.28/6.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 6.28/6.48  thf(sk_A_type, type, sk_A: $i).
% 6.28/6.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.28/6.48  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 6.28/6.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.28/6.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 6.28/6.48  thf(sk_B_type, type, sk_B: $i).
% 6.28/6.48  thf(t173_relat_1, conjecture,
% 6.28/6.48    (![A:$i,B:$i]:
% 6.28/6.48     ( ( v1_relat_1 @ B ) =>
% 6.28/6.48       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 6.28/6.48         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 6.28/6.48  thf(zf_stmt_0, negated_conjecture,
% 6.28/6.48    (~( ![A:$i,B:$i]:
% 6.28/6.48        ( ( v1_relat_1 @ B ) =>
% 6.28/6.48          ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 6.28/6.48            ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )),
% 6.28/6.48    inference('cnf.neg', [status(esa)], [t173_relat_1])).
% 6.28/6.48  thf('0', plain,
% 6.28/6.48      ((~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)
% 6.28/6.48        | ((k10_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('1', plain,
% 6.28/6.48      ((~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))
% 6.28/6.48         <= (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.28/6.48      inference('split', [status(esa)], ['0'])).
% 6.28/6.48  thf('2', plain,
% 6.28/6.48      (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)) | 
% 6.28/6.48       ~ (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 6.28/6.48      inference('split', [status(esa)], ['0'])).
% 6.28/6.48  thf('3', plain,
% 6.28/6.48      (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)
% 6.28/6.48        | ((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('4', plain,
% 6.28/6.48      (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))
% 6.28/6.48         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.28/6.48      inference('split', [status(esa)], ['3'])).
% 6.28/6.48  thf(t3_xboole_0, axiom,
% 6.28/6.48    (![A:$i,B:$i]:
% 6.28/6.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 6.28/6.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 6.28/6.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 6.28/6.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 6.28/6.48  thf('5', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.28/6.48  thf('6', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.28/6.48  thf('7', plain,
% 6.28/6.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 6.28/6.48         (~ (r2_hidden @ X2 @ X0)
% 6.28/6.48          | ~ (r2_hidden @ X2 @ X3)
% 6.28/6.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.28/6.48  thf('8', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.28/6.48         ((r1_xboole_0 @ X1 @ X0)
% 6.28/6.48          | ~ (r1_xboole_0 @ X0 @ X2)
% 6.28/6.48          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 6.28/6.48      inference('sup-', [status(thm)], ['6', '7'])).
% 6.28/6.48  thf('9', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((r1_xboole_0 @ X0 @ X1)
% 6.28/6.48          | ~ (r1_xboole_0 @ X1 @ X0)
% 6.28/6.48          | (r1_xboole_0 @ X0 @ X1))),
% 6.28/6.48      inference('sup-', [status(thm)], ['5', '8'])).
% 6.28/6.48  thf('10', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 6.28/6.48      inference('simplify', [status(thm)], ['9'])).
% 6.28/6.48  thf('11', plain,
% 6.28/6.48      (((r1_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 6.28/6.48         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['4', '10'])).
% 6.28/6.48  thf(d5_relat_1, axiom,
% 6.28/6.48    (![A:$i,B:$i]:
% 6.28/6.48     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 6.28/6.48       ( ![C:$i]:
% 6.28/6.48         ( ( r2_hidden @ C @ B ) <=>
% 6.28/6.48           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 6.28/6.48  thf('12', plain,
% 6.28/6.48      (![X19 : $i, X22 : $i]:
% 6.28/6.48         (((X22) = (k2_relat_1 @ X19))
% 6.28/6.48          | (r2_hidden @ 
% 6.28/6.48             (k4_tarski @ (sk_D_1 @ X22 @ X19) @ (sk_C_1 @ X22 @ X19)) @ X19)
% 6.28/6.48          | (r2_hidden @ (sk_C_1 @ X22 @ X19) @ X22))),
% 6.28/6.48      inference('cnf', [status(esa)], [d5_relat_1])).
% 6.28/6.48  thf(t113_zfmisc_1, axiom,
% 6.28/6.48    (![A:$i,B:$i]:
% 6.28/6.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.28/6.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.28/6.48  thf('13', plain,
% 6.28/6.48      (![X5 : $i, X6 : $i]:
% 6.28/6.48         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 6.28/6.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.28/6.48  thf('14', plain,
% 6.28/6.48      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['13'])).
% 6.28/6.48  thf(t152_zfmisc_1, axiom,
% 6.28/6.48    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 6.28/6.48  thf('15', plain,
% 6.28/6.48      (![X7 : $i, X8 : $i]: ~ (r2_hidden @ X7 @ (k2_zfmisc_1 @ X7 @ X8))),
% 6.28/6.48      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 6.28/6.48  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.28/6.48      inference('sup-', [status(thm)], ['14', '15'])).
% 6.28/6.48  thf('17', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 6.28/6.48          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['12', '16'])).
% 6.28/6.48  thf(t60_relat_1, axiom,
% 6.28/6.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 6.28/6.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.28/6.48  thf('18', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.28/6.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.28/6.48  thf('19', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 6.28/6.48          | ((X0) = (k1_xboole_0)))),
% 6.28/6.48      inference('demod', [status(thm)], ['17', '18'])).
% 6.28/6.48  thf(t166_relat_1, axiom,
% 6.28/6.48    (![A:$i,B:$i,C:$i]:
% 6.28/6.48     ( ( v1_relat_1 @ C ) =>
% 6.28/6.48       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 6.28/6.48         ( ?[D:$i]:
% 6.28/6.48           ( ( r2_hidden @ D @ B ) & 
% 6.28/6.48             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 6.28/6.48             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 6.28/6.48  thf('20', plain,
% 6.28/6.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.28/6.48         (~ (r2_hidden @ X26 @ (k10_relat_1 @ X27 @ X25))
% 6.28/6.48          | (r2_hidden @ (sk_D_3 @ X27 @ X25 @ X26) @ (k2_relat_1 @ X27))
% 6.28/6.48          | ~ (v1_relat_1 @ X27))),
% 6.28/6.48      inference('cnf', [status(esa)], [t166_relat_1])).
% 6.28/6.48  thf('21', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 6.28/6.48          | ~ (v1_relat_1 @ X1)
% 6.28/6.48          | (r2_hidden @ 
% 6.28/6.48             (sk_D_3 @ X1 @ X0 @ 
% 6.28/6.48              (sk_C_1 @ (k10_relat_1 @ X1 @ X0) @ k1_xboole_0)) @ 
% 6.28/6.48             (k2_relat_1 @ X1)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['19', '20'])).
% 6.28/6.48  thf('22', plain,
% 6.28/6.48      (![X0 : $i]:
% 6.28/6.48         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 6.28/6.48          | ((X0) = (k1_xboole_0)))),
% 6.28/6.48      inference('demod', [status(thm)], ['17', '18'])).
% 6.28/6.48  thf('23', plain,
% 6.28/6.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.28/6.48         (~ (r2_hidden @ X26 @ (k10_relat_1 @ X27 @ X25))
% 6.28/6.48          | (r2_hidden @ (sk_D_3 @ X27 @ X25 @ X26) @ X25)
% 6.28/6.48          | ~ (v1_relat_1 @ X27))),
% 6.28/6.48      inference('cnf', [status(esa)], [t166_relat_1])).
% 6.28/6.48  thf('24', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 6.28/6.48          | ~ (v1_relat_1 @ X1)
% 6.28/6.48          | (r2_hidden @ 
% 6.28/6.48             (sk_D_3 @ X1 @ X0 @ 
% 6.28/6.48              (sk_C_1 @ (k10_relat_1 @ X1 @ X0) @ k1_xboole_0)) @ 
% 6.28/6.48             X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['22', '23'])).
% 6.28/6.48  thf('25', plain,
% 6.28/6.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 6.28/6.48         (~ (r2_hidden @ X2 @ X0)
% 6.28/6.48          | ~ (r2_hidden @ X2 @ X3)
% 6.28/6.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.28/6.48  thf('26', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ X1)
% 6.28/6.48          | ((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 6.28/6.48          | ~ (r1_xboole_0 @ X0 @ X2)
% 6.28/6.48          | ~ (r2_hidden @ 
% 6.28/6.48               (sk_D_3 @ X1 @ X0 @ 
% 6.28/6.48                (sk_C_1 @ (k10_relat_1 @ X1 @ X0) @ k1_xboole_0)) @ 
% 6.28/6.48               X2))),
% 6.28/6.48      inference('sup-', [status(thm)], ['24', '25'])).
% 6.28/6.48  thf('27', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ X0)
% 6.28/6.48          | ((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 6.28/6.48          | ~ (r1_xboole_0 @ X1 @ (k2_relat_1 @ X0))
% 6.28/6.48          | ((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 6.28/6.48          | ~ (v1_relat_1 @ X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['21', '26'])).
% 6.28/6.48  thf('28', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         (~ (r1_xboole_0 @ X1 @ (k2_relat_1 @ X0))
% 6.28/6.48          | ((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 6.28/6.48          | ~ (v1_relat_1 @ X0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['27'])).
% 6.28/6.48  thf('29', plain,
% 6.28/6.48      (((~ (v1_relat_1 @ sk_B) | ((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 6.28/6.48         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['11', '28'])).
% 6.28/6.48  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('31', plain,
% 6.28/6.48      ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 6.28/6.48         <= (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.28/6.48      inference('demod', [status(thm)], ['29', '30'])).
% 6.28/6.48  thf('32', plain,
% 6.28/6.48      ((((k10_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 6.28/6.48         <= (~ (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 6.28/6.48      inference('split', [status(esa)], ['0'])).
% 6.28/6.48  thf('33', plain,
% 6.28/6.48      ((((k1_xboole_0) != (k1_xboole_0)))
% 6.28/6.48         <= (~ (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 6.28/6.48             ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.28/6.48      inference('sup-', [status(thm)], ['31', '32'])).
% 6.28/6.48  thf('34', plain,
% 6.28/6.48      ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 6.28/6.48       ~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 6.28/6.48      inference('simplify', [status(thm)], ['33'])).
% 6.28/6.48  thf('35', plain, (~ ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 6.28/6.48      inference('sat_resolution*', [status(thm)], ['2', '34'])).
% 6.28/6.48  thf('36', plain, (~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)),
% 6.28/6.48      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 6.28/6.48  thf('37', plain,
% 6.28/6.48      ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 6.28/6.48         <= ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 6.28/6.48      inference('split', [status(esa)], ['3'])).
% 6.28/6.48  thf('38', plain,
% 6.28/6.48      ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 6.28/6.48       ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 6.28/6.48      inference('split', [status(esa)], ['3'])).
% 6.28/6.48  thf('39', plain, ((((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 6.28/6.48      inference('sat_resolution*', [status(thm)], ['2', '34', '38'])).
% 6.28/6.48  thf('40', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 6.28/6.48      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 6.28/6.48  thf('41', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.28/6.48  thf('42', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 6.28/6.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 6.28/6.48  thf('43', plain,
% 6.28/6.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.28/6.48         (~ (r2_hidden @ X21 @ X20)
% 6.28/6.48          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X21 @ X19) @ X21) @ X19)
% 6.28/6.48          | ((X20) != (k2_relat_1 @ X19)))),
% 6.28/6.48      inference('cnf', [status(esa)], [d5_relat_1])).
% 6.28/6.48  thf('44', plain,
% 6.28/6.48      (![X19 : $i, X21 : $i]:
% 6.28/6.48         ((r2_hidden @ (k4_tarski @ (sk_D_2 @ X21 @ X19) @ X21) @ X19)
% 6.28/6.48          | ~ (r2_hidden @ X21 @ (k2_relat_1 @ X19)))),
% 6.28/6.48      inference('simplify', [status(thm)], ['43'])).
% 6.28/6.48  thf('45', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 6.28/6.48          | (r2_hidden @ 
% 6.28/6.48             (k4_tarski @ (sk_D_2 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 6.28/6.48              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 6.28/6.48             X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['42', '44'])).
% 6.28/6.48  thf(d14_relat_1, axiom,
% 6.28/6.48    (![A:$i]:
% 6.28/6.48     ( ( v1_relat_1 @ A ) =>
% 6.28/6.48       ( ![B:$i,C:$i]:
% 6.28/6.48         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 6.28/6.48           ( ![D:$i]:
% 6.28/6.48             ( ( r2_hidden @ D @ C ) <=>
% 6.28/6.48               ( ?[E:$i]:
% 6.28/6.48                 ( ( r2_hidden @ E @ B ) & 
% 6.28/6.48                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 6.28/6.48  thf('46', plain,
% 6.28/6.48      (![X10 : $i, X11 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 6.28/6.48         (((X13) != (k10_relat_1 @ X11 @ X10))
% 6.28/6.48          | (r2_hidden @ X15 @ X13)
% 6.28/6.48          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X11)
% 6.28/6.48          | ~ (r2_hidden @ X16 @ X10)
% 6.28/6.48          | ~ (v1_relat_1 @ X11))),
% 6.28/6.48      inference('cnf', [status(esa)], [d14_relat_1])).
% 6.28/6.48  thf('47', plain,
% 6.28/6.48      (![X10 : $i, X11 : $i, X15 : $i, X16 : $i]:
% 6.28/6.48         (~ (v1_relat_1 @ X11)
% 6.28/6.48          | ~ (r2_hidden @ X16 @ X10)
% 6.28/6.48          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X11)
% 6.28/6.48          | (r2_hidden @ X15 @ (k10_relat_1 @ X11 @ X10)))),
% 6.28/6.48      inference('simplify', [status(thm)], ['46'])).
% 6.28/6.48  thf('48', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.28/6.48         ((r1_xboole_0 @ (k2_relat_1 @ X0) @ X1)
% 6.28/6.48          | (r2_hidden @ (sk_D_2 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 6.28/6.48             (k10_relat_1 @ X0 @ X2))
% 6.28/6.48          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X2)
% 6.28/6.48          | ~ (v1_relat_1 @ X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['45', '47'])).
% 6.28/6.48  thf('49', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((r1_xboole_0 @ (k2_relat_1 @ X1) @ X0)
% 6.28/6.48          | ~ (v1_relat_1 @ X1)
% 6.28/6.48          | (r2_hidden @ (sk_D_2 @ (sk_C @ X0 @ (k2_relat_1 @ X1)) @ X1) @ 
% 6.28/6.48             (k10_relat_1 @ X1 @ X0))
% 6.28/6.48          | (r1_xboole_0 @ (k2_relat_1 @ X1) @ X0))),
% 6.28/6.48      inference('sup-', [status(thm)], ['41', '48'])).
% 6.28/6.48  thf('50', plain,
% 6.28/6.48      (![X0 : $i, X1 : $i]:
% 6.28/6.48         ((r2_hidden @ (sk_D_2 @ (sk_C @ X0 @ (k2_relat_1 @ X1)) @ X1) @ 
% 6.28/6.48           (k10_relat_1 @ X1 @ X0))
% 6.28/6.48          | ~ (v1_relat_1 @ X1)
% 6.28/6.48          | (r1_xboole_0 @ (k2_relat_1 @ X1) @ X0))),
% 6.28/6.48      inference('simplify', [status(thm)], ['49'])).
% 6.28/6.48  thf('51', plain,
% 6.28/6.48      (((r2_hidden @ (sk_D_2 @ (sk_C @ sk_A @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 6.28/6.48         k1_xboole_0)
% 6.28/6.48        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)
% 6.28/6.48        | ~ (v1_relat_1 @ sk_B))),
% 6.28/6.48      inference('sup+', [status(thm)], ['40', '50'])).
% 6.28/6.48  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 6.28/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.28/6.48  thf('53', plain,
% 6.28/6.48      (((r2_hidden @ (sk_D_2 @ (sk_C @ sk_A @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 6.28/6.48         k1_xboole_0)
% 6.28/6.48        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 6.28/6.48      inference('demod', [status(thm)], ['51', '52'])).
% 6.28/6.48  thf('54', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.28/6.48      inference('sup-', [status(thm)], ['14', '15'])).
% 6.28/6.48  thf('55', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)),
% 6.28/6.48      inference('clc', [status(thm)], ['53', '54'])).
% 6.28/6.48  thf('56', plain, ($false), inference('demod', [status(thm)], ['36', '55'])).
% 6.28/6.48  
% 6.28/6.48  % SZS output end Refutation
% 6.28/6.48  
% 6.32/6.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
