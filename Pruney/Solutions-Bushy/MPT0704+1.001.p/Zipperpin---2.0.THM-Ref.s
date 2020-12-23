%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0704+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.otBSjQW124

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:21 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 237 expanded)
%              Number of leaves         :   33 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  957 (2455 expanded)
%              Number of equality atoms :   45 (  84 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t159_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i] :
          ? [C: $i] :
            ( r1_tarski @ ( k10_relat_1 @ A @ ( k1_tarski @ B ) ) @ ( k1_tarski @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
        <=> ! [B: $i] :
            ? [C: $i] :
              ( r1_tarski @ ( k10_relat_1 @ A @ ( k1_tarski @ B ) ) @ ( k1_tarski @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t159_funct_1])).

thf('0',plain,(
    ! [X34: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) )
      | ~ ( v2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_A )
   <= ~ ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ! [X34: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    ! [X35: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X35 ) ) @ ( k1_tarski @ ( sk_C_3 @ X35 ) ) )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_funct_1 @ sk_A )
   <= ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t56_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
      | ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t56_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( ( k10_relat_1 @ X23 @ X24 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t144_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
              & ! [C: $i] :
                  ( ( k10_relat_1 @ A @ ( k1_tarski @ B ) )
                 != ( k1_tarski @ C ) ) )
      <=> ( v2_funct_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ X20 ) )
      | ( ( k10_relat_1 @ X20 @ ( k1_tarski @ X21 ) )
        = ( k1_tarski @ ( sk_C_2 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t144_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ ( k1_tarski @ X28 ) )
      | ( X27
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('14',plain,(
    ! [X28: $i] :
      ( r1_tarski @ ( k1_tarski @ X28 ) @ ( k1_tarski @ X28 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( sk_C_2 @ X0 @ X1 ) ) )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,
    ( ! [X34: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) )
   <= ! [X34: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( ~ ( v2_funct_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = k1_xboole_0 ) )
   <= ! [X34: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ~ ( v2_funct_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = k1_xboole_0 ) )
   <= ! [X34: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ! [X34: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','20'])).

thf('22',plain,
    ( ! [X34: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) )
   <= ! [X34: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
   <= ( ! [X34: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X25: $i] :
      ( r1_tarski @ k1_xboole_0 @ X25 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,
    ( ~ ! [X34: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X34 ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','25'])).

thf('27',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ! [X35: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X35 ) ) @ ( k1_tarski @ ( sk_C_3 @ X35 ) ) )
   <= ! [X35: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X35 ) ) @ ( k1_tarski @ ( sk_C_3 @ X35 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27
        = ( k1_tarski @ X26 ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) )
          = k1_xboole_0 )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) )
          = ( k1_tarski @ ( sk_C_3 @ X0 ) ) ) )
   <= ! [X35: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X35 ) ) @ ( k1_tarski @ ( sk_C_3 @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k10_relat_1 @ X20 @ ( k1_tarski @ ( sk_B @ X20 ) ) )
       != ( k1_tarski @ X22 ) )
      | ( v2_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t144_funct_1])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
         != ( k1_tarski @ X0 ) )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
          = k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( v2_funct_1 @ sk_A ) )
   <= ! [X35: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X35 ) ) @ ( k1_tarski @ ( sk_C_3 @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
         != ( k1_tarski @ X0 ) )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
          = k1_xboole_0 )
        | ( v2_funct_1 @ sk_A ) )
   <= ! [X35: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X35 ) ) @ ( k1_tarski @ ( sk_C_3 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ( v2_funct_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ! [X35: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X35 ) ) @ ( k1_tarski @ ( sk_C_3 @ X35 ) ) ) ),
    inference(eq_res,[status(thm)],['35'])).

thf('37',plain,
    ( ! [X35: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X35 ) ) @ ( k1_tarski @ ( sk_C_3 @ X35 ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,(
    ! [X35: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X35 ) ) @ ( k1_tarski @ ( sk_C_3 @ X35 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','37'])).

thf('39',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
      = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('40',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('41',plain,
    ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['39','40'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('43',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X20: $i] :
      ( ( r2_hidden @ ( sk_B @ X20 ) @ ( k2_relat_1 @ X20 ) )
      | ( v2_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t144_funct_1])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( X15
        = ( k1_funct_1 @ X12 @ ( sk_D_2 @ X15 @ X12 ) ) )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('46',plain,(
    ! [X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X12 ) )
      | ( X15
        = ( k1_funct_1 @ X12 @ ( sk_D_2 @ X15 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( ( sk_B @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X20: $i] :
      ( ( r2_hidden @ ( sk_B @ X20 ) @ ( k2_relat_1 @ X20 ) )
      | ( v2_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t144_funct_1])).

thf('50',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_2 @ X15 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('51',plain,(
    ! [X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_2 @ X15 @ X12 ) @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( X3
       != ( k10_relat_1 @ X2 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X5 ) @ X1 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('55',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X2 @ X5 ) @ X1 )
      | ( r2_hidden @ X5 @ ( k10_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_B @ X0 ) @ X0 ) @ ( k10_relat_1 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['43','59'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('61',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k10_relat_1 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','62'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('64',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('65',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('66',plain,(
    ! [X31: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('67',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_A ),
    inference(demod,[status(thm)],['63','68','69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['27','71'])).


%------------------------------------------------------------------------------
