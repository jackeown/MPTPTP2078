%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1RnmU2p1Li

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:16 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 318 expanded)
%              Number of leaves         :   28 ( 105 expanded)
%              Depth                    :   27
%              Number of atoms          : 1052 (3001 expanded)
%              Number of equality atoms :   59 ( 191 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t151_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
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

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) ) )
      | ( r2_hidden @ X25 @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) ) )
      | ( r2_hidden @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_xboole_0 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X1 )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ sk_A ) ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X7 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('28',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('32',plain,(
    ! [X22: $i] :
      ( ( r1_tarski @ X22 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X22 ) @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','38','39'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('41',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k7_relat_1 @ X28 @ X29 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('44',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ k1_xboole_0 )
      = ( k6_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) ) )
      | ( r2_hidden @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X7 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['46','56'])).

thf('58',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('60',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('62',plain,
    ( ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('63',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k1_xboole_0
      = ( k9_relat_1 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','68'])).

thf('70',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','69'])).

thf('71',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('73',plain,
    ( ( ( r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('78',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','68','77'])).

thf('79',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('81',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ k1_xboole_0 )
    = ( k6_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('83',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('85',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('86',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('88',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('89',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X27 ) )
      | ( r2_hidden @ X25 @ ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['86','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('95',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('98',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['70','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1RnmU2p1Li
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.28/1.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.28/1.52  % Solved by: fo/fo7.sh
% 1.28/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.52  % done 1938 iterations in 1.060s
% 1.28/1.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.28/1.52  % SZS output start Refutation
% 1.28/1.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.28/1.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.28/1.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.28/1.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.28/1.52  thf(sk_B_type, type, sk_B: $i).
% 1.28/1.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.28/1.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.28/1.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.28/1.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.28/1.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.28/1.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.28/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.28/1.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.28/1.52  thf(t151_relat_1, conjecture,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( v1_relat_1 @ B ) =>
% 1.28/1.52       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 1.28/1.52         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.28/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.52    (~( ![A:$i,B:$i]:
% 1.28/1.52        ( ( v1_relat_1 @ B ) =>
% 1.28/1.52          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 1.28/1.52            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 1.28/1.52    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 1.28/1.52  thf('0', plain,
% 1.28/1.52      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.28/1.52        | ((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('1', plain,
% 1.28/1.52      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.28/1.52         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('split', [status(esa)], ['0'])).
% 1.28/1.52  thf('2', plain,
% 1.28/1.52      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 1.28/1.52       ~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.28/1.52      inference('split', [status(esa)], ['0'])).
% 1.28/1.52  thf('3', plain,
% 1.28/1.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.28/1.52        | ((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('4', plain,
% 1.28/1.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('split', [status(esa)], ['3'])).
% 1.28/1.52  thf(symmetry_r1_xboole_0, axiom,
% 1.28/1.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.28/1.52  thf('5', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.28/1.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.28/1.52  thf('6', plain,
% 1.28/1.52      (((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['4', '5'])).
% 1.28/1.52  thf(t3_xboole_0, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.28/1.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.28/1.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.28/1.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.28/1.52  thf('7', plain,
% 1.28/1.52      (![X2 : $i, X3 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 1.28/1.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.28/1.52  thf(t86_relat_1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( v1_relat_1 @ C ) =>
% 1.28/1.52       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 1.28/1.52         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 1.28/1.52  thf('8', plain,
% 1.28/1.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X25 @ (k1_relat_1 @ (k7_relat_1 @ X27 @ X26)))
% 1.28/1.52          | (r2_hidden @ X25 @ (k1_relat_1 @ X27))
% 1.28/1.52          | ~ (v1_relat_1 @ X27))),
% 1.28/1.52      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.28/1.52  thf('9', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 1.28/1.52          | ~ (v1_relat_1 @ X1)
% 1.28/1.52          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 1.28/1.52             (k1_relat_1 @ X1)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['7', '8'])).
% 1.28/1.52  thf('10', plain,
% 1.28/1.52      (![X2 : $i, X3 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 1.28/1.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.28/1.52  thf('11', plain,
% 1.28/1.52      (![X2 : $i, X4 : $i, X5 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X4 @ X2)
% 1.28/1.52          | ~ (r2_hidden @ X4 @ X5)
% 1.28/1.52          | ~ (r1_xboole_0 @ X2 @ X5))),
% 1.28/1.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.28/1.52  thf('12', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X1 @ X0)
% 1.28/1.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.28/1.52          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.28/1.52      inference('sup-', [status(thm)], ['10', '11'])).
% 1.28/1.52  thf('13', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         (~ (v1_relat_1 @ X0)
% 1.28/1.52          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 1.28/1.52          | ~ (r1_xboole_0 @ X2 @ (k1_relat_1 @ X0))
% 1.28/1.52          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2))),
% 1.28/1.52      inference('sup-', [status(thm)], ['9', '12'])).
% 1.28/1.52  thf('14', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         (~ (r1_xboole_0 @ X2 @ (k1_relat_1 @ X0))
% 1.28/1.52          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 1.28/1.52          | ~ (v1_relat_1 @ X0))),
% 1.28/1.52      inference('simplify', [status(thm)], ['13'])).
% 1.28/1.52  thf('15', plain,
% 1.28/1.52      ((![X0 : $i]:
% 1.28/1.52          (~ (v1_relat_1 @ sk_B)
% 1.28/1.52           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A)))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['6', '14'])).
% 1.28/1.52  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('17', plain,
% 1.28/1.52      ((![X0 : $i]:
% 1.28/1.52          (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('demod', [status(thm)], ['15', '16'])).
% 1.28/1.52  thf('18', plain,
% 1.28/1.52      (![X2 : $i, X3 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 1.28/1.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.28/1.52  thf('19', plain,
% 1.28/1.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X25 @ (k1_relat_1 @ (k7_relat_1 @ X27 @ X26)))
% 1.28/1.52          | (r2_hidden @ X25 @ X26)
% 1.28/1.52          | ~ (v1_relat_1 @ X27))),
% 1.28/1.52      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.28/1.52  thf('20', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.28/1.52          | ~ (v1_relat_1 @ X1)
% 1.28/1.52          | (r2_hidden @ (sk_C @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2) @ 
% 1.28/1.52             X0))),
% 1.28/1.52      inference('sup-', [status(thm)], ['18', '19'])).
% 1.28/1.52  thf('21', plain,
% 1.28/1.52      (![X2 : $i, X3 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 1.28/1.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.28/1.52  thf('22', plain,
% 1.28/1.52      (![X2 : $i, X4 : $i, X5 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X4 @ X2)
% 1.28/1.52          | ~ (r2_hidden @ X4 @ X5)
% 1.28/1.52          | ~ (r1_xboole_0 @ X2 @ X5))),
% 1.28/1.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.28/1.52  thf('23', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X0 @ X1)
% 1.28/1.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.28/1.52          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.28/1.52      inference('sup-', [status(thm)], ['21', '22'])).
% 1.28/1.52  thf('24', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         (~ (v1_relat_1 @ X2)
% 1.28/1.52          | (r1_xboole_0 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X0)))
% 1.28/1.52          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.28/1.52          | (r1_xboole_0 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X0))))),
% 1.28/1.52      inference('sup-', [status(thm)], ['20', '23'])).
% 1.28/1.52  thf('25', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         (~ (r1_xboole_0 @ X1 @ X0)
% 1.28/1.52          | (r1_xboole_0 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X0)))
% 1.28/1.52          | ~ (v1_relat_1 @ X2))),
% 1.28/1.52      inference('simplify', [status(thm)], ['24'])).
% 1.28/1.52  thf('26', plain,
% 1.28/1.52      ((![X0 : $i, X1 : $i]:
% 1.28/1.52          (~ (v1_relat_1 @ X1)
% 1.28/1.52           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ 
% 1.28/1.52              (k1_relat_1 @ (k7_relat_1 @ X1 @ sk_A)))))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['17', '25'])).
% 1.28/1.52  thf(t66_xboole_1, axiom,
% 1.28/1.52    (![A:$i]:
% 1.28/1.52     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 1.28/1.52       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.28/1.52  thf('27', plain,
% 1.28/1.52      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X7 @ X7))),
% 1.28/1.52      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.28/1.52  thf('28', plain,
% 1.28/1.52      (((~ (v1_relat_1 @ sk_B)
% 1.28/1.52         | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['26', '27'])).
% 1.28/1.52  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('30', plain,
% 1.28/1.52      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0)))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('demod', [status(thm)], ['28', '29'])).
% 1.28/1.52  thf(t148_relat_1, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( v1_relat_1 @ B ) =>
% 1.28/1.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.28/1.52  thf('31', plain,
% 1.28/1.52      (![X20 : $i, X21 : $i]:
% 1.28/1.52         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.28/1.52          | ~ (v1_relat_1 @ X20))),
% 1.28/1.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.28/1.52  thf(t21_relat_1, axiom,
% 1.28/1.52    (![A:$i]:
% 1.28/1.52     ( ( v1_relat_1 @ A ) =>
% 1.28/1.52       ( r1_tarski @
% 1.28/1.52         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.28/1.52  thf('32', plain,
% 1.28/1.52      (![X22 : $i]:
% 1.28/1.52         ((r1_tarski @ X22 @ 
% 1.28/1.52           (k2_zfmisc_1 @ (k1_relat_1 @ X22) @ (k2_relat_1 @ X22)))
% 1.28/1.52          | ~ (v1_relat_1 @ X22))),
% 1.28/1.52      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.28/1.52  thf('33', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 1.28/1.52           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.28/1.52            (k9_relat_1 @ X1 @ X0)))
% 1.28/1.52          | ~ (v1_relat_1 @ X1)
% 1.28/1.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.28/1.52      inference('sup+', [status(thm)], ['31', '32'])).
% 1.28/1.52  thf(dt_k7_relat_1, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.28/1.52  thf('34', plain,
% 1.28/1.52      (![X14 : $i, X15 : $i]:
% 1.28/1.52         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 1.28/1.52      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.28/1.52  thf('35', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         (~ (v1_relat_1 @ X1)
% 1.28/1.52          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 1.28/1.52             (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.28/1.52              (k9_relat_1 @ X1 @ X0))))),
% 1.28/1.52      inference('clc', [status(thm)], ['33', '34'])).
% 1.28/1.52  thf('36', plain,
% 1.28/1.52      ((((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 1.28/1.52          (k2_zfmisc_1 @ k1_xboole_0 @ (k9_relat_1 @ sk_B @ sk_A)))
% 1.28/1.52         | ~ (v1_relat_1 @ sk_B)))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('sup+', [status(thm)], ['30', '35'])).
% 1.28/1.52  thf(t113_zfmisc_1, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.28/1.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.28/1.52  thf('37', plain,
% 1.28/1.52      (![X9 : $i, X10 : $i]:
% 1.28/1.52         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 1.28/1.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.28/1.52  thf('38', plain,
% 1.28/1.52      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 1.28/1.52      inference('simplify', [status(thm)], ['37'])).
% 1.28/1.52  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('40', plain,
% 1.28/1.52      (((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ k1_xboole_0))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('demod', [status(thm)], ['36', '38', '39'])).
% 1.28/1.52  thf(t71_relat_1, axiom,
% 1.28/1.52    (![A:$i]:
% 1.28/1.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.28/1.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.28/1.52  thf('41', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.28/1.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.28/1.52  thf(t97_relat_1, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( v1_relat_1 @ B ) =>
% 1.28/1.52       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.28/1.52         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.28/1.52  thf('42', plain,
% 1.28/1.52      (![X28 : $i, X29 : $i]:
% 1.28/1.52         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 1.28/1.52          | ((k7_relat_1 @ X28 @ X29) = (X28))
% 1.28/1.52          | ~ (v1_relat_1 @ X28))),
% 1.28/1.52      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.28/1.52  thf('43', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         (~ (r1_tarski @ X0 @ X1)
% 1.28/1.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.28/1.52          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['41', '42'])).
% 1.28/1.52  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.28/1.52  thf('44', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.28/1.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.28/1.52  thf('45', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         (~ (r1_tarski @ X0 @ X1)
% 1.28/1.52          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 1.28/1.52      inference('demod', [status(thm)], ['43', '44'])).
% 1.28/1.52  thf('46', plain,
% 1.28/1.52      ((((k7_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ k1_xboole_0)
% 1.28/1.52          = (k6_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['40', '45'])).
% 1.28/1.52  thf('47', plain,
% 1.28/1.52      (![X2 : $i, X3 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 1.28/1.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.28/1.52  thf('48', plain,
% 1.28/1.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X25 @ (k1_relat_1 @ (k7_relat_1 @ X27 @ X26)))
% 1.28/1.52          | (r2_hidden @ X25 @ X26)
% 1.28/1.52          | ~ (v1_relat_1 @ X27))),
% 1.28/1.52      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.28/1.52  thf('49', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 1.28/1.52          | ~ (v1_relat_1 @ X1)
% 1.28/1.52          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 1.28/1.52             X0))),
% 1.28/1.52      inference('sup-', [status(thm)], ['47', '48'])).
% 1.28/1.52  thf('50', plain,
% 1.28/1.52      (![X9 : $i, X10 : $i]:
% 1.28/1.52         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 1.28/1.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.28/1.52  thf('51', plain,
% 1.28/1.52      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 1.28/1.52      inference('simplify', [status(thm)], ['50'])).
% 1.28/1.52  thf(t152_zfmisc_1, axiom,
% 1.28/1.52    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.28/1.52  thf('52', plain,
% 1.28/1.52      (![X11 : $i, X12 : $i]: ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X11 @ X12))),
% 1.28/1.52      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 1.28/1.52  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.28/1.52      inference('sup-', [status(thm)], ['51', '52'])).
% 1.28/1.52  thf('54', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         (~ (v1_relat_1 @ X0)
% 1.28/1.52          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) @ X1))),
% 1.28/1.52      inference('sup-', [status(thm)], ['49', '53'])).
% 1.28/1.52  thf('55', plain,
% 1.28/1.52      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X7 @ X7))),
% 1.28/1.52      inference('cnf', [status(esa)], [t66_xboole_1])).
% 1.28/1.52  thf('56', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         (~ (v1_relat_1 @ X0)
% 1.28/1.52          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['54', '55'])).
% 1.28/1.52  thf('57', plain,
% 1.28/1.52      (((((k1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.28/1.52           = (k1_xboole_0))
% 1.28/1.52         | ~ (v1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('sup+', [status(thm)], ['46', '56'])).
% 1.28/1.52  thf('58', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.28/1.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.28/1.52  thf('59', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.28/1.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.28/1.52  thf('60', plain,
% 1.28/1.52      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.28/1.52  thf('61', plain,
% 1.28/1.52      (![X20 : $i, X21 : $i]:
% 1.28/1.52         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.28/1.52          | ~ (v1_relat_1 @ X20))),
% 1.28/1.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.28/1.52  thf('62', plain,
% 1.28/1.52      (((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A))
% 1.28/1.52         | ~ (v1_relat_1 @ sk_B)))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('sup+', [status(thm)], ['60', '61'])).
% 1.28/1.52  thf(t60_relat_1, axiom,
% 1.28/1.52    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.28/1.52     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.28/1.52  thf('63', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.28/1.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.28/1.52  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('65', plain,
% 1.28/1.52      ((((k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A)))
% 1.28/1.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.28/1.52  thf('66', plain,
% 1.28/1.52      ((((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 1.28/1.52         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 1.28/1.52      inference('split', [status(esa)], ['0'])).
% 1.28/1.52  thf('67', plain,
% 1.28/1.52      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.28/1.52         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 1.28/1.52             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['65', '66'])).
% 1.28/1.52  thf('68', plain,
% 1.28/1.52      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 1.28/1.52       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.28/1.52      inference('simplify', [status(thm)], ['67'])).
% 1.28/1.52  thf('69', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.28/1.52      inference('sat_resolution*', [status(thm)], ['2', '68'])).
% 1.28/1.52  thf('70', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 1.28/1.52      inference('simpl_trail', [status(thm)], ['1', '69'])).
% 1.28/1.52  thf('71', plain,
% 1.28/1.52      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 1.28/1.52         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 1.28/1.52      inference('split', [status(esa)], ['3'])).
% 1.28/1.52  thf('72', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         (~ (v1_relat_1 @ X1)
% 1.28/1.52          | (r1_tarski @ (k7_relat_1 @ X1 @ X0) @ 
% 1.28/1.52             (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 1.28/1.52              (k9_relat_1 @ X1 @ X0))))),
% 1.28/1.52      inference('clc', [status(thm)], ['33', '34'])).
% 1.28/1.52  thf('73', plain,
% 1.28/1.52      ((((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 1.28/1.52          (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ 
% 1.28/1.52           k1_xboole_0))
% 1.28/1.52         | ~ (v1_relat_1 @ sk_B)))
% 1.28/1.52         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 1.28/1.52      inference('sup+', [status(thm)], ['71', '72'])).
% 1.28/1.52  thf('74', plain,
% 1.28/1.52      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 1.28/1.52      inference('simplify', [status(thm)], ['50'])).
% 1.28/1.52  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('76', plain,
% 1.28/1.52      (((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ k1_xboole_0))
% 1.28/1.52         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 1.28/1.52      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.28/1.52  thf('77', plain,
% 1.28/1.52      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 1.28/1.52       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.28/1.52      inference('split', [status(esa)], ['3'])).
% 1.28/1.52  thf('78', plain, ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.28/1.52      inference('sat_resolution*', [status(thm)], ['2', '68', '77'])).
% 1.28/1.52  thf('79', plain, ((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ k1_xboole_0)),
% 1.28/1.52      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 1.28/1.52  thf('80', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         (~ (r1_tarski @ X0 @ X1)
% 1.28/1.52          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 1.28/1.52      inference('demod', [status(thm)], ['43', '44'])).
% 1.28/1.52  thf('81', plain,
% 1.28/1.52      (((k7_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ k1_xboole_0)
% 1.28/1.52         = (k6_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['79', '80'])).
% 1.28/1.52  thf('82', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         (~ (v1_relat_1 @ X0)
% 1.28/1.52          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['54', '55'])).
% 1.28/1.52  thf('83', plain,
% 1.28/1.52      ((((k1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.28/1.52          = (k1_xboole_0))
% 1.28/1.52        | ~ (v1_relat_1 @ (k6_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 1.28/1.52      inference('sup+', [status(thm)], ['81', '82'])).
% 1.28/1.52  thf('84', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.28/1.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.28/1.52  thf('85', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 1.28/1.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.28/1.52  thf('86', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.28/1.52      inference('demod', [status(thm)], ['83', '84', '85'])).
% 1.28/1.52  thf('87', plain,
% 1.28/1.52      (![X2 : $i, X3 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 1.28/1.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.28/1.52  thf('88', plain,
% 1.28/1.52      (![X2 : $i, X3 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 1.28/1.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.28/1.52  thf('89', plain,
% 1.28/1.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X25 @ X26)
% 1.28/1.52          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X27))
% 1.28/1.52          | (r2_hidden @ X25 @ (k1_relat_1 @ (k7_relat_1 @ X27 @ X26)))
% 1.28/1.52          | ~ (v1_relat_1 @ X27))),
% 1.28/1.52      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.28/1.52  thf('90', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 1.28/1.52          | ~ (v1_relat_1 @ X0)
% 1.28/1.52          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 1.28/1.52             (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 1.28/1.52          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 1.28/1.52      inference('sup-', [status(thm)], ['88', '89'])).
% 1.28/1.52  thf('91', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 1.28/1.52          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 1.28/1.52             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.28/1.52          | ~ (v1_relat_1 @ X1)
% 1.28/1.52          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 1.28/1.52      inference('sup-', [status(thm)], ['87', '90'])).
% 1.28/1.52  thf('92', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         (~ (v1_relat_1 @ X1)
% 1.28/1.52          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 1.28/1.52             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.28/1.52          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 1.28/1.52      inference('simplify', [status(thm)], ['91'])).
% 1.28/1.52  thf('93', plain,
% 1.28/1.52      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B)) @ 
% 1.28/1.52         (k1_relat_1 @ k1_xboole_0))
% 1.28/1.52        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.28/1.52        | ~ (v1_relat_1 @ sk_B))),
% 1.28/1.52      inference('sup+', [status(thm)], ['86', '92'])).
% 1.28/1.52  thf('94', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.28/1.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.28/1.52  thf('95', plain, ((v1_relat_1 @ sk_B)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('96', plain,
% 1.28/1.52      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B)) @ k1_xboole_0)
% 1.28/1.52        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.28/1.52      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.28/1.52  thf('97', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.28/1.52      inference('sup-', [status(thm)], ['51', '52'])).
% 1.28/1.52  thf('98', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 1.28/1.52      inference('clc', [status(thm)], ['96', '97'])).
% 1.28/1.52  thf('99', plain, ($false), inference('demod', [status(thm)], ['70', '98'])).
% 1.28/1.52  
% 1.28/1.52  % SZS output end Refutation
% 1.28/1.52  
% 1.28/1.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
