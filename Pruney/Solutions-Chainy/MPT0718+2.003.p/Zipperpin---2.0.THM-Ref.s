%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WvdIMYk0LS

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:24 EST 2020

% Result     : Theorem 13.34s
% Output     : Refutation 13.34s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 169 expanded)
%              Number of leaves         :   40 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  632 (1381 expanded)
%              Number of equality atoms :   43 (  93 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v2_relat_1_type,type,(
    v2_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d15_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_relat_1 @ A )
      <=> ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( v1_xboole_0 @ ( k1_funct_1 @ A @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_1 @ X20 @ ( sk_B @ X20 ) ) )
      | ( v2_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d15_funct_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_relat_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t173_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v5_funct_1 @ A @ B )
              & ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) ) )
           => ( v2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v5_funct_1 @ A @ B )
                & ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) ) )
             => ( v2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t173_funct_1])).

thf('3',plain,(
    v5_funct_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X20: $i] :
      ( ( r2_hidden @ ( sk_B @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( v2_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d15_funct_1])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ~ ( v2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v5_funct_1 @ X22 @ X23 )
      | ( r2_hidden @ ( k1_funct_1 @ X22 @ X24 ) @ ( k1_funct_1 @ X23 @ X24 ) )
      | ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( v5_funct_1 @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( v5_funct_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( v2_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['2','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( v2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['24','25'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X9 @ ( k1_tarski @ X8 ) )
        = ( k1_tarski @ X8 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('29',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('33',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t137_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X16: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X16 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33','39'])).

thf('41',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['28','40'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 != X10 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X10 ) )
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X10 ) )
     != ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33','39'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('50',plain,(
    ! [X17: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','38'])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X16: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X16 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf(fc9_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('56',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X25 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['52','53','61'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','64'])).

thf('66',plain,(
    ! [X10: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X10 ) ) ),
    inference(demod,[status(thm)],['43','65'])).

thf('67',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WvdIMYk0LS
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 13.34/13.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.34/13.56  % Solved by: fo/fo7.sh
% 13.34/13.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.34/13.56  % done 9623 iterations in 13.100s
% 13.34/13.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.34/13.56  % SZS output start Refutation
% 13.34/13.56  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 13.34/13.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 13.34/13.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 13.34/13.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.34/13.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 13.34/13.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.34/13.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 13.34/13.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 13.34/13.56  thf(sk_A_type, type, sk_A: $i).
% 13.34/13.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 13.34/13.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 13.34/13.56  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 13.34/13.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 13.34/13.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 13.34/13.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 13.34/13.56  thf(v2_relat_1_type, type, v2_relat_1: $i > $o).
% 13.34/13.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.34/13.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 13.34/13.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 13.34/13.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.34/13.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 13.34/13.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 13.34/13.56  thf(sk_B_type, type, sk_B: $i > $i).
% 13.34/13.56  thf(d15_funct_1, axiom,
% 13.34/13.56    (![A:$i]:
% 13.34/13.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.34/13.56       ( ( v2_relat_1 @ A ) <=>
% 13.34/13.56         ( ![B:$i]:
% 13.34/13.56           ( ~( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 13.34/13.56                ( v1_xboole_0 @ ( k1_funct_1 @ A @ B ) ) ) ) ) ) ))).
% 13.34/13.56  thf('0', plain,
% 13.34/13.56      (![X20 : $i]:
% 13.34/13.56         ((v1_xboole_0 @ (k1_funct_1 @ X20 @ (sk_B @ X20)))
% 13.34/13.56          | (v2_relat_1 @ X20)
% 13.34/13.56          | ~ (v1_funct_1 @ X20)
% 13.34/13.56          | ~ (v1_relat_1 @ X20))),
% 13.34/13.56      inference('cnf', [status(esa)], [d15_funct_1])).
% 13.34/13.56  thf(l13_xboole_0, axiom,
% 13.34/13.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 13.34/13.56  thf('1', plain,
% 13.34/13.56      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 13.34/13.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 13.34/13.56  thf('2', plain,
% 13.34/13.56      (![X0 : $i]:
% 13.34/13.56         (~ (v1_relat_1 @ X0)
% 13.34/13.56          | ~ (v1_funct_1 @ X0)
% 13.34/13.56          | (v2_relat_1 @ X0)
% 13.34/13.56          | ((k1_funct_1 @ X0 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 13.34/13.56      inference('sup-', [status(thm)], ['0', '1'])).
% 13.34/13.56  thf(t173_funct_1, conjecture,
% 13.34/13.56    (![A:$i]:
% 13.34/13.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.34/13.56       ( ![B:$i]:
% 13.34/13.56         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.34/13.56           ( ( ( v5_funct_1 @ A @ B ) & 
% 13.34/13.56               ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) ) =>
% 13.34/13.56             ( v2_relat_1 @ B ) ) ) ) ))).
% 13.34/13.56  thf(zf_stmt_0, negated_conjecture,
% 13.34/13.56    (~( ![A:$i]:
% 13.34/13.56        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.34/13.56          ( ![B:$i]:
% 13.34/13.56            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.34/13.56              ( ( ( v5_funct_1 @ A @ B ) & 
% 13.34/13.56                  ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) ) =>
% 13.34/13.56                ( v2_relat_1 @ B ) ) ) ) ) )),
% 13.34/13.56    inference('cnf.neg', [status(esa)], [t173_funct_1])).
% 13.34/13.56  thf('3', plain, ((v5_funct_1 @ sk_A @ sk_B_1)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('4', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('5', plain,
% 13.34/13.56      (![X20 : $i]:
% 13.34/13.56         ((r2_hidden @ (sk_B @ X20) @ (k1_relat_1 @ X20))
% 13.34/13.56          | (v2_relat_1 @ X20)
% 13.34/13.56          | ~ (v1_funct_1 @ X20)
% 13.34/13.56          | ~ (v1_relat_1 @ X20))),
% 13.34/13.56      inference('cnf', [status(esa)], [d15_funct_1])).
% 13.34/13.56  thf('6', plain,
% 13.34/13.56      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 13.34/13.56        | ~ (v1_relat_1 @ sk_B_1)
% 13.34/13.56        | ~ (v1_funct_1 @ sk_B_1)
% 13.34/13.56        | (v2_relat_1 @ sk_B_1))),
% 13.34/13.56      inference('sup+', [status(thm)], ['4', '5'])).
% 13.34/13.56  thf('7', plain, ((v1_relat_1 @ sk_B_1)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('8', plain, ((v1_funct_1 @ sk_B_1)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('9', plain,
% 13.34/13.56      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 13.34/13.56        | (v2_relat_1 @ sk_B_1))),
% 13.34/13.56      inference('demod', [status(thm)], ['6', '7', '8'])).
% 13.34/13.56  thf('10', plain, (~ (v2_relat_1 @ sk_B_1)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('11', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))),
% 13.34/13.56      inference('clc', [status(thm)], ['9', '10'])).
% 13.34/13.56  thf(d20_funct_1, axiom,
% 13.34/13.56    (![A:$i]:
% 13.34/13.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.34/13.56       ( ![B:$i]:
% 13.34/13.56         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.34/13.56           ( ( v5_funct_1 @ B @ A ) <=>
% 13.34/13.56             ( ![C:$i]:
% 13.34/13.56               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 13.34/13.56                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 13.34/13.56  thf('12', plain,
% 13.34/13.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 13.34/13.56         (~ (v1_relat_1 @ X22)
% 13.34/13.56          | ~ (v1_funct_1 @ X22)
% 13.34/13.56          | ~ (v5_funct_1 @ X22 @ X23)
% 13.34/13.56          | (r2_hidden @ (k1_funct_1 @ X22 @ X24) @ (k1_funct_1 @ X23 @ X24))
% 13.34/13.56          | ~ (r2_hidden @ X24 @ (k1_relat_1 @ X22))
% 13.34/13.56          | ~ (v1_funct_1 @ X23)
% 13.34/13.56          | ~ (v1_relat_1 @ X23))),
% 13.34/13.56      inference('cnf', [status(esa)], [d20_funct_1])).
% 13.34/13.56  thf('13', plain,
% 13.34/13.56      (![X0 : $i]:
% 13.34/13.56         (~ (v1_relat_1 @ X0)
% 13.34/13.56          | ~ (v1_funct_1 @ X0)
% 13.34/13.56          | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 13.34/13.56             (k1_funct_1 @ X0 @ (sk_B @ sk_B_1)))
% 13.34/13.56          | ~ (v5_funct_1 @ sk_A @ X0)
% 13.34/13.56          | ~ (v1_funct_1 @ sk_A)
% 13.34/13.56          | ~ (v1_relat_1 @ sk_A))),
% 13.34/13.56      inference('sup-', [status(thm)], ['11', '12'])).
% 13.34/13.56  thf('14', plain, ((v1_funct_1 @ sk_A)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('16', plain,
% 13.34/13.56      (![X0 : $i]:
% 13.34/13.56         (~ (v1_relat_1 @ X0)
% 13.34/13.56          | ~ (v1_funct_1 @ X0)
% 13.34/13.56          | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 13.34/13.56             (k1_funct_1 @ X0 @ (sk_B @ sk_B_1)))
% 13.34/13.56          | ~ (v5_funct_1 @ sk_A @ X0))),
% 13.34/13.56      inference('demod', [status(thm)], ['13', '14', '15'])).
% 13.34/13.56  thf('17', plain,
% 13.34/13.56      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 13.34/13.56         (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 13.34/13.56        | ~ (v1_funct_1 @ sk_B_1)
% 13.34/13.56        | ~ (v1_relat_1 @ sk_B_1))),
% 13.34/13.56      inference('sup-', [status(thm)], ['3', '16'])).
% 13.34/13.56  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('19', plain, ((v1_relat_1 @ sk_B_1)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('20', plain,
% 13.34/13.56      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 13.34/13.56        (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 13.34/13.56      inference('demod', [status(thm)], ['17', '18', '19'])).
% 13.34/13.56  thf('21', plain,
% 13.34/13.56      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ k1_xboole_0)
% 13.34/13.56        | (v2_relat_1 @ sk_B_1)
% 13.34/13.56        | ~ (v1_funct_1 @ sk_B_1)
% 13.34/13.56        | ~ (v1_relat_1 @ sk_B_1))),
% 13.34/13.56      inference('sup+', [status(thm)], ['2', '20'])).
% 13.34/13.56  thf('22', plain, ((v1_funct_1 @ sk_B_1)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('23', plain, ((v1_relat_1 @ sk_B_1)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('24', plain,
% 13.34/13.56      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ k1_xboole_0)
% 13.34/13.56        | (v2_relat_1 @ sk_B_1))),
% 13.34/13.56      inference('demod', [status(thm)], ['21', '22', '23'])).
% 13.34/13.56  thf('25', plain, (~ (v2_relat_1 @ sk_B_1)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('26', plain,
% 13.34/13.56      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ k1_xboole_0)),
% 13.34/13.56      inference('clc', [status(thm)], ['24', '25'])).
% 13.34/13.56  thf(l31_zfmisc_1, axiom,
% 13.34/13.56    (![A:$i,B:$i]:
% 13.34/13.56     ( ( r2_hidden @ A @ B ) =>
% 13.34/13.56       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 13.34/13.56  thf('27', plain,
% 13.34/13.56      (![X8 : $i, X9 : $i]:
% 13.34/13.56         (((k3_xboole_0 @ X9 @ (k1_tarski @ X8)) = (k1_tarski @ X8))
% 13.34/13.56          | ~ (r2_hidden @ X8 @ X9))),
% 13.34/13.56      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 13.34/13.56  thf('28', plain,
% 13.34/13.56      (((k3_xboole_0 @ k1_xboole_0 @ 
% 13.34/13.56         (k1_tarski @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1))))
% 13.34/13.56         = (k1_tarski @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1))))),
% 13.34/13.56      inference('sup-', [status(thm)], ['26', '27'])).
% 13.34/13.56  thf(t60_relat_1, axiom,
% 13.34/13.56    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 13.34/13.56     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 13.34/13.56  thf('29', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 13.34/13.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 13.34/13.56  thf(t90_relat_1, axiom,
% 13.34/13.56    (![A:$i,B:$i]:
% 13.34/13.56     ( ( v1_relat_1 @ B ) =>
% 13.34/13.56       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 13.34/13.56         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 13.34/13.56  thf('30', plain,
% 13.34/13.56      (![X18 : $i, X19 : $i]:
% 13.34/13.56         (((k1_relat_1 @ (k7_relat_1 @ X18 @ X19))
% 13.34/13.56            = (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 13.34/13.56          | ~ (v1_relat_1 @ X18))),
% 13.34/13.56      inference('cnf', [status(esa)], [t90_relat_1])).
% 13.34/13.56  thf('31', plain,
% 13.34/13.56      (![X0 : $i]:
% 13.34/13.56         (((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0))
% 13.34/13.56            = (k3_xboole_0 @ k1_xboole_0 @ X0))
% 13.34/13.56          | ~ (v1_relat_1 @ k1_xboole_0))),
% 13.34/13.56      inference('sup+', [status(thm)], ['29', '30'])).
% 13.34/13.56  thf(t111_relat_1, axiom,
% 13.34/13.56    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 13.34/13.56  thf('32', plain,
% 13.34/13.56      (![X15 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 13.34/13.56      inference('cnf', [status(esa)], [t111_relat_1])).
% 13.34/13.56  thf('33', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 13.34/13.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 13.34/13.56  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf(t137_relat_1, axiom,
% 13.34/13.56    (![A:$i]:
% 13.34/13.56     ( ( v1_relat_1 @ A ) =>
% 13.34/13.56       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 13.34/13.56  thf('35', plain,
% 13.34/13.56      (![X16 : $i]:
% 13.34/13.56         (((k8_relat_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))
% 13.34/13.56          | ~ (v1_relat_1 @ X16))),
% 13.34/13.56      inference('cnf', [status(esa)], [t137_relat_1])).
% 13.34/13.56  thf(dt_k8_relat_1, axiom,
% 13.34/13.56    (![A:$i,B:$i]:
% 13.34/13.56     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 13.34/13.56  thf('36', plain,
% 13.34/13.56      (![X13 : $i, X14 : $i]:
% 13.34/13.56         ((v1_relat_1 @ (k8_relat_1 @ X13 @ X14)) | ~ (v1_relat_1 @ X14))),
% 13.34/13.56      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 13.34/13.56  thf('37', plain,
% 13.34/13.56      (![X0 : $i]:
% 13.34/13.56         ((v1_relat_1 @ k1_xboole_0)
% 13.34/13.56          | ~ (v1_relat_1 @ X0)
% 13.34/13.56          | ~ (v1_relat_1 @ X0))),
% 13.34/13.56      inference('sup+', [status(thm)], ['35', '36'])).
% 13.34/13.56  thf('38', plain,
% 13.34/13.56      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 13.34/13.56      inference('simplify', [status(thm)], ['37'])).
% 13.34/13.56  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 13.34/13.56      inference('sup-', [status(thm)], ['34', '38'])).
% 13.34/13.56  thf('40', plain,
% 13.34/13.56      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 13.34/13.56      inference('demod', [status(thm)], ['31', '32', '33', '39'])).
% 13.34/13.56  thf('41', plain,
% 13.34/13.56      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1))))),
% 13.34/13.56      inference('demod', [status(thm)], ['28', '40'])).
% 13.34/13.56  thf(t20_zfmisc_1, axiom,
% 13.34/13.56    (![A:$i,B:$i]:
% 13.34/13.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 13.34/13.56         ( k1_tarski @ A ) ) <=>
% 13.34/13.56       ( ( A ) != ( B ) ) ))).
% 13.34/13.56  thf('42', plain,
% 13.34/13.56      (![X10 : $i, X11 : $i]:
% 13.34/13.56         (((X11) != (X10))
% 13.34/13.56          | ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X10))
% 13.34/13.56              != (k1_tarski @ X11)))),
% 13.34/13.56      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 13.34/13.56  thf('43', plain,
% 13.34/13.56      (![X10 : $i]:
% 13.34/13.56         ((k4_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X10))
% 13.34/13.56           != (k1_tarski @ X10))),
% 13.34/13.56      inference('simplify', [status(thm)], ['42'])).
% 13.34/13.56  thf('44', plain,
% 13.34/13.56      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 13.34/13.56      inference('demod', [status(thm)], ['31', '32', '33', '39'])).
% 13.34/13.56  thf(d7_xboole_0, axiom,
% 13.34/13.56    (![A:$i,B:$i]:
% 13.34/13.56     ( ( r1_xboole_0 @ A @ B ) <=>
% 13.34/13.56       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 13.34/13.56  thf('45', plain,
% 13.34/13.56      (![X0 : $i, X2 : $i]:
% 13.34/13.56         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 13.34/13.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 13.34/13.56  thf('46', plain,
% 13.34/13.56      (![X0 : $i]:
% 13.34/13.56         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 13.34/13.56      inference('sup-', [status(thm)], ['44', '45'])).
% 13.34/13.56  thf('47', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 13.34/13.56      inference('simplify', [status(thm)], ['46'])).
% 13.34/13.56  thf(t88_xboole_1, axiom,
% 13.34/13.56    (![A:$i,B:$i]:
% 13.34/13.56     ( ( r1_xboole_0 @ A @ B ) =>
% 13.34/13.56       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 13.34/13.56  thf('48', plain,
% 13.34/13.56      (![X6 : $i, X7 : $i]:
% 13.34/13.56         (((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7) = (X6))
% 13.34/13.56          | ~ (r1_xboole_0 @ X6 @ X7))),
% 13.34/13.56      inference('cnf', [status(esa)], [t88_xboole_1])).
% 13.34/13.56  thf('49', plain,
% 13.34/13.56      (![X0 : $i]:
% 13.34/13.56         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 13.34/13.56      inference('sup-', [status(thm)], ['47', '48'])).
% 13.34/13.56  thf(t150_relat_1, axiom,
% 13.34/13.56    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 13.34/13.56  thf('50', plain,
% 13.34/13.56      (![X17 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 13.34/13.56      inference('cnf', [status(esa)], [t150_relat_1])).
% 13.34/13.56  thf(t145_funct_1, axiom,
% 13.34/13.56    (![A:$i,B:$i]:
% 13.34/13.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.34/13.56       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 13.34/13.56  thf('51', plain,
% 13.34/13.56      (![X27 : $i, X28 : $i]:
% 13.34/13.56         ((r1_tarski @ (k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X28)) @ X28)
% 13.34/13.56          | ~ (v1_funct_1 @ X27)
% 13.34/13.56          | ~ (v1_relat_1 @ X27))),
% 13.34/13.56      inference('cnf', [status(esa)], [t145_funct_1])).
% 13.34/13.56  thf('52', plain,
% 13.34/13.56      (![X0 : $i]:
% 13.34/13.56         ((r1_tarski @ k1_xboole_0 @ X0)
% 13.34/13.56          | ~ (v1_relat_1 @ k1_xboole_0)
% 13.34/13.56          | ~ (v1_funct_1 @ k1_xboole_0))),
% 13.34/13.56      inference('sup+', [status(thm)], ['50', '51'])).
% 13.34/13.56  thf('53', plain, ((v1_relat_1 @ k1_xboole_0)),
% 13.34/13.56      inference('sup-', [status(thm)], ['34', '38'])).
% 13.34/13.56  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('55', plain,
% 13.34/13.56      (![X16 : $i]:
% 13.34/13.56         (((k8_relat_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))
% 13.34/13.56          | ~ (v1_relat_1 @ X16))),
% 13.34/13.56      inference('cnf', [status(esa)], [t137_relat_1])).
% 13.34/13.56  thf(fc9_funct_1, axiom,
% 13.34/13.56    (![A:$i,B:$i]:
% 13.34/13.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.34/13.56       ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) & 
% 13.34/13.56         ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ))).
% 13.34/13.56  thf('56', plain,
% 13.34/13.56      (![X25 : $i, X26 : $i]:
% 13.34/13.56         ((v1_funct_1 @ (k8_relat_1 @ X25 @ X26))
% 13.34/13.56          | ~ (v1_funct_1 @ X26)
% 13.34/13.56          | ~ (v1_relat_1 @ X26))),
% 13.34/13.56      inference('cnf', [status(esa)], [fc9_funct_1])).
% 13.34/13.56  thf('57', plain,
% 13.34/13.56      (![X0 : $i]:
% 13.34/13.56         ((v1_funct_1 @ k1_xboole_0)
% 13.34/13.56          | ~ (v1_relat_1 @ X0)
% 13.34/13.56          | ~ (v1_relat_1 @ X0)
% 13.34/13.56          | ~ (v1_funct_1 @ X0))),
% 13.34/13.56      inference('sup+', [status(thm)], ['55', '56'])).
% 13.34/13.56  thf('58', plain,
% 13.34/13.56      (![X0 : $i]:
% 13.34/13.56         (~ (v1_funct_1 @ X0)
% 13.34/13.56          | ~ (v1_relat_1 @ X0)
% 13.34/13.56          | (v1_funct_1 @ k1_xboole_0))),
% 13.34/13.56      inference('simplify', [status(thm)], ['57'])).
% 13.34/13.56  thf('59', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_funct_1 @ sk_A))),
% 13.34/13.56      inference('sup-', [status(thm)], ['54', '58'])).
% 13.34/13.56  thf('60', plain, ((v1_funct_1 @ sk_A)),
% 13.34/13.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.34/13.56  thf('61', plain, ((v1_funct_1 @ k1_xboole_0)),
% 13.34/13.56      inference('demod', [status(thm)], ['59', '60'])).
% 13.34/13.56  thf('62', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 13.34/13.56      inference('demod', [status(thm)], ['52', '53', '61'])).
% 13.34/13.56  thf(t12_xboole_1, axiom,
% 13.34/13.56    (![A:$i,B:$i]:
% 13.34/13.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 13.34/13.56  thf('63', plain,
% 13.34/13.56      (![X4 : $i, X5 : $i]:
% 13.34/13.56         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 13.34/13.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 13.34/13.56  thf('64', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 13.34/13.56      inference('sup-', [status(thm)], ['62', '63'])).
% 13.34/13.56  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 13.34/13.56      inference('demod', [status(thm)], ['49', '64'])).
% 13.34/13.56  thf('66', plain, (![X10 : $i]: ((k1_xboole_0) != (k1_tarski @ X10))),
% 13.34/13.56      inference('demod', [status(thm)], ['43', '65'])).
% 13.34/13.56  thf('67', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 13.34/13.56      inference('sup-', [status(thm)], ['41', '66'])).
% 13.34/13.56  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 13.34/13.56  
% 13.34/13.56  % SZS output end Refutation
% 13.34/13.56  
% 13.34/13.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
