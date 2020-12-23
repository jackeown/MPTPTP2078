%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0437+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LRLkUEPXdo

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 8.94s
% Output     : Refutation 8.94s
% Verified   : 
% Statistics : Number of formulae       :   28 (  38 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  159 ( 295 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_29_type,type,(
    sk_C_29: $i )).

thf(sk_B_13_type,type,(
    sk_B_13: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_4_type,type,(
    sk_A_4: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t20_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ ( A @ B ) @ C ) )
       => ( ( r2_hidden @ ( A @ ( k1_relat_1 @ C ) ) )
          & ( r2_hidden @ ( B @ ( k2_relat_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ ( A @ B ) @ C ) )
         => ( ( r2_hidden @ ( A @ ( k1_relat_1 @ C ) ) )
            & ( r2_hidden @ ( B @ ( k2_relat_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( sk_A_4 @ ( k1_relat_1 @ sk_C_29 ) ) )
    | ~ ( r2_hidden @ ( sk_B_13 @ ( k2_relat_1 @ sk_C_29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( sk_B_13 @ ( k2_relat_1 @ sk_C_29 ) ) )
   <= ~ ( r2_hidden @ ( sk_B_13 @ ( k2_relat_1 @ sk_C_29 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_A_4 @ sk_B_13 ) @ sk_C_29 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ ( C @ D ) @ A ) ) ) ) )).

thf('3',plain,(
    ! [X2041: $i,X2042: $i,X2043: $i,X2044: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( X2041 @ X2042 ) @ X2043 ) )
      | ( r2_hidden @ ( X2041 @ X2044 ) )
      | ( X2044
       != ( k1_relat_1 @ X2043 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X2041: $i,X2042: $i,X2043: $i] :
      ( ( r2_hidden @ ( X2041 @ ( k1_relat_1 @ X2043 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( X2041 @ X2042 ) @ X2043 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r2_hidden @ ( sk_A_4 @ ( k1_relat_1 @ sk_C_29 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ~ ( r2_hidden @ ( sk_A_4 @ ( k1_relat_1 @ sk_C_29 ) ) )
   <= ~ ( r2_hidden @ ( sk_A_4 @ ( k1_relat_1 @ sk_C_29 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    r2_hidden @ ( sk_A_4 @ ( k1_relat_1 @ sk_C_29 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ ( sk_B_13 @ ( k2_relat_1 @ sk_C_29 ) ) )
    | ~ ( r2_hidden @ ( sk_A_4 @ ( k1_relat_1 @ sk_C_29 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    ~ ( r2_hidden @ ( sk_B_13 @ ( k2_relat_1 @ sk_C_29 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ ( sk_B_13 @ ( k2_relat_1 @ sk_C_29 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','9'])).

thf('11',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_A_4 @ sk_B_13 ) @ sk_C_29 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ ( D @ C ) @ A ) ) ) ) )).

thf('12',plain,(
    ! [X2048: $i,X2049: $i,X2050: $i,X2051: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( X2048 @ X2049 ) @ X2050 ) )
      | ( r2_hidden @ ( X2049 @ X2051 ) )
      | ( X2051
       != ( k2_relat_1 @ X2050 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('13',plain,(
    ! [X2048: $i,X2049: $i,X2050: $i] :
      ( ( r2_hidden @ ( X2049 @ ( k2_relat_1 @ X2050 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( X2048 @ X2049 ) @ X2050 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_hidden @ ( sk_B_13 @ ( k2_relat_1 @ sk_C_29 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['10','14'])).

%------------------------------------------------------------------------------
