%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mnKrs7tITy

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:57 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 550 expanded)
%              Number of leaves         :   29 ( 174 expanded)
%              Depth                    :   16
%              Number of atoms          :  801 (4565 expanded)
%              Number of equality atoms :   56 ( 291 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ( r2_hidden @ ( sk_C_2 @ X20 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X53: $i,X55: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X53 ) @ X55 )
      | ~ ( r2_hidden @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ sk_A ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ( r2_hidden @ ( sk_C_2 @ X20 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X28 @ X29 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i,X35: $i] :
      ( ( r1_xboole_0 @ X32 @ X33 )
      | ~ ( r1_xboole_0 @ X32 @ ( k2_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18 = X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X18 ) @ X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X27: $i] :
      ( ( k2_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('28',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','31'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('33',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X30 @ X31 ) @ ( k4_xboole_0 @ X30 @ X31 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('34',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X27: $i] :
      ( ( k2_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('36',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k2_xboole_0 @ X39 @ X40 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X39 @ X40 ) @ ( k3_xboole_0 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf('40',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','31'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('45',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['24'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('53',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','31'])).

thf('55',plain,(
    ! [X27: $i] :
      ( ( k2_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('56',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','56'])).

thf('58',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ( r2_hidden @ ( sk_C_2 @ X20 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ( r2_hidden @ ( sk_C_2 @ X20 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('64',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ( r2_hidden @ ( sk_C_2 @ X20 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('65',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('70',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ X36 @ X37 )
        = X36 )
      | ~ ( r1_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k2_xboole_0 @ X41 @ X42 )
      = ( k5_xboole_0 @ X41 @ ( k4_xboole_0 @ X42 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['58','73'])).

thf('75',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('76',plain,(
    ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('78',plain,(
    ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mnKrs7tITy
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 1452 iterations in 0.627s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.08  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(t3_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.90/1.08            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.08       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.08            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.90/1.08  thf('0', plain,
% 0.90/1.08      (![X19 : $i, X20 : $i]:
% 0.90/1.08         ((r1_xboole_0 @ X19 @ X20) | (r2_hidden @ (sk_C_2 @ X20 @ X19) @ X20))),
% 0.90/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.08  thf(t140_zfmisc_1, conjecture,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r2_hidden @ A @ B ) =>
% 0.90/1.08       ( ( k2_xboole_0 @
% 0.90/1.08           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.90/1.08         ( B ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i,B:$i]:
% 0.90/1.08        ( ( r2_hidden @ A @ B ) =>
% 0.90/1.08          ( ( k2_xboole_0 @
% 0.90/1.08              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.90/1.08            ( B ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.90/1.08  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(l1_zfmisc_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      (![X53 : $i, X55 : $i]:
% 0.90/1.08         ((r1_tarski @ (k1_tarski @ X53) @ X55) | ~ (r2_hidden @ X53 @ X55))),
% 0.90/1.08      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.90/1.08  thf('3', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.90/1.08      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.08  thf(d3_tarski, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.08  thf('4', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X0 @ X1)
% 0.90/1.08          | (r2_hidden @ X0 @ X2)
% 0.90/1.08          | ~ (r1_tarski @ X1 @ X2))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('5', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 0.90/1.08          | (r2_hidden @ (sk_C_2 @ (k1_tarski @ sk_A) @ X0) @ sk_B))),
% 0.90/1.08      inference('sup-', [status(thm)], ['0', '5'])).
% 0.90/1.08  thf('7', plain,
% 0.90/1.08      (![X19 : $i, X20 : $i]:
% 0.90/1.08         ((r1_xboole_0 @ X19 @ X20) | (r2_hidden @ (sk_C_2 @ X20 @ X19) @ X19))),
% 0.90/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.08  thf(d5_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.90/1.08       ( ![D:$i]:
% 0.90/1.08         ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.08           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X8 @ X7)
% 0.90/1.08          | ~ (r2_hidden @ X8 @ X6)
% 0.90/1.08          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.90/1.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X8 @ X6)
% 0.90/1.08          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['8'])).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.90/1.08          | ~ (r2_hidden @ (sk_C_2 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['7', '9'])).
% 0.90/1.08  thf('11', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_A))
% 0.90/1.08          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['6', '10'])).
% 0.90/1.08  thf('12', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_A))),
% 0.90/1.08      inference('simplify', [status(thm)], ['11'])).
% 0.90/1.08  thf(t36_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.08  thf('13', plain,
% 0.90/1.08      (![X28 : $i, X29 : $i]: (r1_tarski @ (k4_xboole_0 @ X28 @ X29) @ X28)),
% 0.90/1.08      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.90/1.08  thf(t12_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.90/1.08  thf('14', plain,
% 0.90/1.08      (![X25 : $i, X26 : $i]:
% 0.90/1.08         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 0.90/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.08  thf(t70_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.90/1.08            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.90/1.08       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.90/1.08            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.90/1.08  thf('16', plain,
% 0.90/1.08      (![X32 : $i, X33 : $i, X35 : $i]:
% 0.90/1.08         ((r1_xboole_0 @ X32 @ X33)
% 0.90/1.08          | ~ (r1_xboole_0 @ X32 @ (k2_xboole_0 @ X33 @ X35)))),
% 0.90/1.08      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.90/1.08  thf('17', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r1_xboole_0 @ X2 @ X0)
% 0.90/1.08          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['15', '16'])).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 0.90/1.08          (k4_xboole_0 @ (k1_tarski @ sk_A) @ X1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['12', '17'])).
% 0.90/1.08  thf(t2_tarski, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.90/1.08       ( ( A ) = ( B ) ) ))).
% 0.90/1.08  thf('19', plain,
% 0.90/1.08      (![X17 : $i, X18 : $i]:
% 0.90/1.08         (((X18) = (X17))
% 0.90/1.08          | (r2_hidden @ (sk_C_1 @ X17 @ X18) @ X17)
% 0.90/1.08          | (r2_hidden @ (sk_C_1 @ X17 @ X18) @ X18))),
% 0.90/1.08      inference('cnf', [status(esa)], [t2_tarski])).
% 0.90/1.08  thf('20', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.08  thf(t1_boole, axiom,
% 0.90/1.08    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.08  thf('21', plain, (![X27 : $i]: ((k2_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 0.90/1.08      inference('cnf', [status(esa)], [t1_boole])).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.90/1.08      inference('sup+', [status(thm)], ['20', '21'])).
% 0.90/1.08  thf('23', plain,
% 0.90/1.08      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X8 @ X6)
% 0.90/1.08          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.90/1.08      inference('simplify', [status(thm)], ['8'])).
% 0.90/1.08  thf('24', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.08  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.08      inference('condensation', [status(thm)], ['24'])).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.90/1.08          | ((X0) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['19', '25'])).
% 0.90/1.08  thf('27', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.90/1.08          | ((X0) = (k1_xboole_0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['19', '25'])).
% 0.90/1.08  thf('28', plain,
% 0.90/1.08      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X21 @ X19)
% 0.90/1.08          | ~ (r2_hidden @ X21 @ X22)
% 0.90/1.08          | ~ (r1_xboole_0 @ X19 @ X22))),
% 0.90/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.08  thf('29', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (((X0) = (k1_xboole_0))
% 0.90/1.08          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.90/1.08          | ~ (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.09  thf('30', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (((X0) = (k1_xboole_0))
% 0.90/1.09          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.90/1.09          | ((X0) = (k1_xboole_0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['26', '29'])).
% 0.90/1.09  thf('31', plain,
% 0.90/1.09      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.09      inference('simplify', [status(thm)], ['30'])).
% 0.90/1.09  thf('32', plain,
% 0.90/1.09      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['18', '31'])).
% 0.90/1.09  thf(t51_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.90/1.09       ( A ) ))).
% 0.90/1.09  thf('33', plain,
% 0.90/1.09      (![X30 : $i, X31 : $i]:
% 0.90/1.09         ((k2_xboole_0 @ (k3_xboole_0 @ X30 @ X31) @ (k4_xboole_0 @ X30 @ X31))
% 0.90/1.09           = (X30))),
% 0.90/1.09      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.90/1.09  thf('34', plain,
% 0.90/1.09      (((k2_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ k1_xboole_0)
% 0.90/1.09         = (k1_tarski @ sk_A))),
% 0.90/1.09      inference('sup+', [status(thm)], ['32', '33'])).
% 0.90/1.09  thf('35', plain, (![X27 : $i]: ((k2_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 0.90/1.09      inference('cnf', [status(esa)], [t1_boole])).
% 0.90/1.09  thf('36', plain,
% 0.90/1.09      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.90/1.09      inference('demod', [status(thm)], ['34', '35'])).
% 0.90/1.09  thf(t94_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( k2_xboole_0 @ A @ B ) =
% 0.90/1.09       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.09  thf('37', plain,
% 0.90/1.09      (![X39 : $i, X40 : $i]:
% 0.90/1.09         ((k2_xboole_0 @ X39 @ X40)
% 0.90/1.09           = (k5_xboole_0 @ (k5_xboole_0 @ X39 @ X40) @ 
% 0.90/1.09              (k3_xboole_0 @ X39 @ X40)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.90/1.09  thf('38', plain,
% 0.90/1.09      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.90/1.09         = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.90/1.09            (k1_tarski @ sk_A)))),
% 0.90/1.09      inference('sup+', [status(thm)], ['36', '37'])).
% 0.90/1.09  thf('39', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.90/1.09      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.09  thf('40', plain,
% 0.90/1.09      (![X25 : $i, X26 : $i]:
% 0.90/1.09         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 0.90/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.90/1.09  thf('41', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['39', '40'])).
% 0.90/1.09  thf('42', plain,
% 0.90/1.09      (((sk_B)
% 0.90/1.09         = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.90/1.09            (k1_tarski @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['38', '41'])).
% 0.90/1.09  thf('43', plain,
% 0.90/1.09      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['18', '31'])).
% 0.90/1.09  thf(d6_xboole_0, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( k5_xboole_0 @ A @ B ) =
% 0.90/1.09       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.90/1.09  thf('44', plain,
% 0.90/1.09      (![X10 : $i, X11 : $i]:
% 0.90/1.09         ((k5_xboole_0 @ X10 @ X11)
% 0.90/1.09           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ 
% 0.90/1.09              (k4_xboole_0 @ X11 @ X10)))),
% 0.90/1.09      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.90/1.09  thf('45', plain,
% 0.90/1.09      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.90/1.09         = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.90/1.09            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['43', '44'])).
% 0.90/1.09  thf('46', plain,
% 0.90/1.09      (![X1 : $i, X3 : $i]:
% 0.90/1.09         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.90/1.09      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.09  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.09      inference('condensation', [status(thm)], ['24'])).
% 0.90/1.09  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.09      inference('sup-', [status(thm)], ['46', '47'])).
% 0.90/1.09  thf('49', plain,
% 0.90/1.09      (![X25 : $i, X26 : $i]:
% 0.90/1.09         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 0.90/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.90/1.09  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['48', '49'])).
% 0.90/1.09  thf('51', plain,
% 0.90/1.09      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.90/1.09         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['45', '50'])).
% 0.90/1.09  thf('52', plain,
% 0.90/1.09      (![X10 : $i, X11 : $i]:
% 0.90/1.09         ((k5_xboole_0 @ X10 @ X11)
% 0.90/1.09           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ 
% 0.90/1.09              (k4_xboole_0 @ X11 @ X10)))),
% 0.90/1.09      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.90/1.09  thf('53', plain,
% 0.90/1.09      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.90/1.09         = (k2_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.90/1.09            (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.90/1.09      inference('sup+', [status(thm)], ['51', '52'])).
% 0.90/1.09  thf('54', plain,
% 0.90/1.09      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['18', '31'])).
% 0.90/1.09  thf('55', plain, (![X27 : $i]: ((k2_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 0.90/1.09      inference('cnf', [status(esa)], [t1_boole])).
% 0.90/1.09  thf('56', plain,
% 0.90/1.09      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.90/1.09         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.90/1.09  thf('57', plain,
% 0.90/1.09      (((sk_B)
% 0.90/1.09         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.90/1.09            (k1_tarski @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['42', '56'])).
% 0.90/1.09  thf('58', plain,
% 0.90/1.09      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.90/1.09         (k1_tarski @ sk_A)) != (sk_B))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('59', plain,
% 0.90/1.09      (![X19 : $i, X20 : $i]:
% 0.90/1.09         ((r1_xboole_0 @ X19 @ X20) | (r2_hidden @ (sk_C_2 @ X20 @ X19) @ X20))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.09  thf('60', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.90/1.09          | ~ (r2_hidden @ (sk_C_2 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['7', '9'])).
% 0.90/1.09  thf('61', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.90/1.09          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['59', '60'])).
% 0.90/1.09  thf('62', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.90/1.09      inference('simplify', [status(thm)], ['61'])).
% 0.90/1.09  thf('63', plain,
% 0.90/1.09      (![X19 : $i, X20 : $i]:
% 0.90/1.09         ((r1_xboole_0 @ X19 @ X20) | (r2_hidden @ (sk_C_2 @ X20 @ X19) @ X19))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.09  thf('64', plain,
% 0.90/1.09      (![X19 : $i, X20 : $i]:
% 0.90/1.09         ((r1_xboole_0 @ X19 @ X20) | (r2_hidden @ (sk_C_2 @ X20 @ X19) @ X20))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.09  thf('65', plain,
% 0.90/1.09      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X21 @ X19)
% 0.90/1.09          | ~ (r2_hidden @ X21 @ X22)
% 0.90/1.09          | ~ (r1_xboole_0 @ X19 @ X22))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.09  thf('66', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         ((r1_xboole_0 @ X1 @ X0)
% 0.90/1.09          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.90/1.09          | ~ (r2_hidden @ (sk_C_2 @ X0 @ X1) @ X2))),
% 0.90/1.09      inference('sup-', [status(thm)], ['64', '65'])).
% 0.90/1.09  thf('67', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((r1_xboole_0 @ X0 @ X1)
% 0.90/1.09          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.90/1.09          | (r1_xboole_0 @ X0 @ X1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['63', '66'])).
% 0.90/1.09  thf('68', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.90/1.09      inference('simplify', [status(thm)], ['67'])).
% 0.90/1.09  thf('69', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['62', '68'])).
% 0.90/1.09  thf(t83_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.90/1.09  thf('70', plain,
% 0.90/1.09      (![X36 : $i, X37 : $i]:
% 0.90/1.09         (((k4_xboole_0 @ X36 @ X37) = (X36)) | ~ (r1_xboole_0 @ X36 @ X37))),
% 0.90/1.09      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.90/1.09  thf('71', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.09  thf(t98_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.90/1.09  thf('72', plain,
% 0.90/1.09      (![X41 : $i, X42 : $i]:
% 0.90/1.09         ((k2_xboole_0 @ X41 @ X42)
% 0.90/1.09           = (k5_xboole_0 @ X41 @ (k4_xboole_0 @ X42 @ X41)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.09  thf('73', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.90/1.09           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.90/1.09      inference('sup+', [status(thm)], ['71', '72'])).
% 0.90/1.09  thf('74', plain,
% 0.90/1.09      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.90/1.09         (k1_tarski @ sk_A)) != (sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['58', '73'])).
% 0.90/1.09  thf('75', plain,
% 0.90/1.09      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.90/1.09         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['45', '50'])).
% 0.90/1.09  thf('76', plain,
% 0.90/1.09      (((k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.90/1.09         (k1_tarski @ sk_A)) != (sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['74', '75'])).
% 0.90/1.09  thf('77', plain,
% 0.90/1.09      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.90/1.09         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.90/1.09  thf('78', plain,
% 0.90/1.09      (((k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.90/1.09         (k1_tarski @ sk_A)) != (sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['76', '77'])).
% 0.90/1.09  thf('79', plain, ($false),
% 0.90/1.09      inference('simplify_reflect-', [status(thm)], ['57', '78'])).
% 0.90/1.09  
% 0.90/1.09  % SZS output end Refutation
% 0.90/1.09  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
