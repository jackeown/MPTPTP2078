%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0260+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LGlVypcb0b

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:52 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  122 ( 138 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_10_type,type,(
    sk_C_10: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t55_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ ( A @ B ) @ C ) )
        & ( r2_hidden @ ( A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_xboole_0 @ ( k2_tarski @ ( A @ B ) @ C ) )
          & ( r2_hidden @ ( A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_zfmisc_1])).

thf('0',plain,(
    r1_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ ( sk_C_10 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ ( sk_A_2 @ sk_C_10 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
              & ( r2_hidden @ ( C @ A ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ ( C @ A ) )
                & ( r2_hidden @ ( C @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X58: $i,X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ ( X60 @ X58 ) )
      | ~ ( r2_hidden @ ( X60 @ X61 ) )
      | ~ ( r1_xboole_0 @ ( X58 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_C_10 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( r2_hidden @ ( sk_A_2 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ C ) )
    <=> ( ( r2_hidden @ ( A @ C ) )
        & ( r2_hidden @ ( B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X1105: $i,X1106: $i,X1107: $i] :
      ( ( r2_hidden @ ( X1105 @ X1106 ) )
      | ~ ( r1_tarski @ ( k2_tarski @ ( X1105 @ X1107 ) @ X1106 ) ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( X1 @ ( k2_tarski @ ( X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    $false ),
    inference(demod,[status(thm)],['6','10'])).

%------------------------------------------------------------------------------
