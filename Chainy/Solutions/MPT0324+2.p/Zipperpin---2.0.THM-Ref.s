%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0324+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FWTGL4KyH2

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 8.32s
% Output     : Refutation 8.32s
% Verified   : 
% Statistics : Number of formulae       :   21 (  25 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  146 ( 222 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_E_7_type,type,(
    sk_E_7: $i )).

thf(sk_D_14_type,type,(
    sk_D_14: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_13_type,type,(
    sk_C_13: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_4_type,type,(
    sk_B_4: $i )).

thf(t137_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
        & ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( D @ E ) ) ) ) )
     => ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( B @ D ) @ ( k3_xboole_0 @ ( C @ E ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( B @ C ) ) ) )
          & ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( D @ E ) ) ) ) )
       => ( r2_hidden @ ( A @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( B @ D ) @ ( k3_xboole_0 @ ( C @ E ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t137_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( sk_A_2 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( sk_B_4 @ sk_D_14 ) @ ( k3_xboole_0 @ ( sk_C_13 @ sk_E_7 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( C @ D ) ) ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( A @ C ) @ ( k2_zfmisc_1 @ ( B @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X1124: $i,X1125: $i,X1126: $i,X1127: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( X1124 @ X1126 ) @ ( k3_xboole_0 @ ( X1125 @ X1127 ) ) ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( X1124 @ X1125 ) @ ( k2_zfmisc_1 @ ( X1126 @ X1127 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('2',plain,(
    r2_hidden @ ( sk_A_2 @ ( k2_zfmisc_1 @ ( sk_B_4 @ sk_C_13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r2_hidden @ ( sk_A_2 @ ( k2_zfmisc_1 @ ( sk_D_14 @ sk_E_7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            & ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( X23 @ X24 ) )
      | ~ ( r2_hidden @ ( X23 @ X25 ) )
      | ( r2_hidden @ ( X23 @ X26 ) )
      | ( X26
       != ( k3_xboole_0 @ ( X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ ( X23 @ ( k3_xboole_0 @ ( X24 @ X25 ) ) ) )
      | ~ ( r2_hidden @ ( X23 @ X25 ) )
      | ~ ( r2_hidden @ ( X23 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_A_2 @ X0 ) )
      | ( r2_hidden @ ( sk_A_2 @ ( k3_xboole_0 @ ( X0 @ ( k2_zfmisc_1 @ ( sk_D_14 @ sk_E_7 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r2_hidden @ ( sk_A_2 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( sk_B_4 @ sk_C_13 ) @ ( k2_zfmisc_1 @ ( sk_D_14 @ sk_E_7 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['0','1','7'])).

%------------------------------------------------------------------------------
