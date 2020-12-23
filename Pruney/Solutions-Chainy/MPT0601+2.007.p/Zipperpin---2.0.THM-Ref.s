%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c7wfCWgngF

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:42 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 130 expanded)
%              Number of leaves         :   33 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  756 (1088 expanded)
%              Number of equality atoms :   66 (  97 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('0',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k11_relat_1 @ X23 @ X24 )
        = ( k9_relat_1 @ X23 @ ( k1_tarski @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k9_relat_1 @ X25 @ X26 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 )
      | ( ( k7_relat_1 @ X32 @ X33 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('26',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X31 ) )
      | ( r2_hidden @ X29 @ ( k1_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','30'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('32',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('37',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('38',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ X22 )
      | ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( ( k7_relat_1 @ X28 @ X27 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X32 @ X33 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('49',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( ( k9_relat_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('54',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k11_relat_1 @ X23 @ X24 )
        = ( k9_relat_1 @ X23 @ ( k1_tarski @ X24 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('58',plain,
    ( ( ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c7wfCWgngF
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:16:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 96 iterations in 0.058s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.19/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(t205_relat_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.50         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( ( v1_relat_1 @ B ) =>
% 0.19/0.50          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.19/0.50            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.19/0.50        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.50       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.19/0.50         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf(d16_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X23 : $i, X24 : $i]:
% 0.19/0.50         (((k11_relat_1 @ X23 @ X24) = (k9_relat_1 @ X23 @ (k1_tarski @ X24)))
% 0.19/0.50          | ~ (v1_relat_1 @ X23))),
% 0.19/0.50      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.19/0.50  thf(t151_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X25 : $i, X26 : $i]:
% 0.19/0.50         (((k9_relat_1 @ X25 @ X26) != (k1_xboole_0))
% 0.19/0.50          | (r1_xboole_0 @ (k1_relat_1 @ X25) @ X26)
% 0.19/0.50          | ~ (v1_relat_1 @ X25))),
% 0.19/0.50      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.50         | ~ (v1_relat_1 @ sk_B)
% 0.19/0.50         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.19/0.50         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '6'])).
% 0.19/0.50  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.50         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.19/0.50         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.19/0.50         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.50  thf(t95_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X32 : $i, X33 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ (k1_relat_1 @ X32) @ X33)
% 0.19/0.50          | ((k7_relat_1 @ X32 @ X33) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ X32))),
% 0.19/0.50      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (((~ (v1_relat_1 @ sk_B)
% 0.19/0.50         | ((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))
% 0.19/0.50         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      ((((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.19/0.50         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.50  thf(t69_enumset1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf(t70_enumset1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X19 : $i, X20 : $i]:
% 0.19/0.50         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.19/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.50  thf(d1_enumset1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.50       ( ![E:$i]:
% 0.19/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.19/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.19/0.50  thf(zf_stmt_2, axiom,
% 0.19/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.19/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.19/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_3, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.50       ( ![E:$i]:
% 0.19/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.50         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.19/0.50          | (r2_hidden @ X11 @ X15)
% 0.19/0.50          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.50         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 0.19/0.50          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.19/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.50          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.50      inference('sup+', [status(thm)], ['16', '18'])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (((X7) != (X6)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X6 @ X8 @ X9 @ X6)),
% 0.19/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['19', '21'])).
% 0.19/0.50  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['15', '22'])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.19/0.50        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('split', [status(esa)], ['24'])).
% 0.19/0.50  thf(t86_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ C ) =>
% 0.19/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.19/0.50         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X29 @ X30)
% 0.19/0.50          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ X31))
% 0.19/0.50          | (r2_hidden @ X29 @ (k1_relat_1 @ (k7_relat_1 @ X31 @ X30)))
% 0.19/0.50          | ~ (v1_relat_1 @ X31))),
% 0.19/0.50      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      ((![X0 : $i]:
% 0.19/0.50          (~ (v1_relat_1 @ sk_B)
% 0.19/0.50           | (r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 0.19/0.50           | ~ (r2_hidden @ sk_A @ X0)))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      ((![X0 : $i]:
% 0.19/0.50          ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 0.19/0.50           | ~ (r2_hidden @ sk_A @ X0)))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ 
% 0.19/0.50         (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['23', '29'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ k1_xboole_0)))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.19/0.50             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['14', '30'])).
% 0.19/0.50  thf(t60_relat_1, axiom,
% 0.19/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.50  thf('32', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ k1_xboole_0))
% 0.19/0.50         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.19/0.50             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf(t2_boole, axiom,
% 0.19/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.50  thf(t4_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.19/0.50          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.50  thf('37', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.50  thf('38', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.19/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.50       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['33', '38'])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.50       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.50      inference('split', [status(esa)], ['24'])).
% 0.19/0.50  thf(l27_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ (k1_tarski @ X21) @ X22) | (r2_hidden @ X21 @ X22))),
% 0.19/0.50      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.19/0.50  thf(t187_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.19/0.50           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (![X27 : $i, X28 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ X27 @ (k1_relat_1 @ X28))
% 0.19/0.50          | ((k7_relat_1 @ X28 @ X27) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ X28))),
% 0.19/0.50      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.19/0.50          | ~ (v1_relat_1 @ X0)
% 0.19/0.50          | ((k7_relat_1 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      (((((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.19/0.50         | ~ (v1_relat_1 @ sk_B)))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.50  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      ((((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X32 : $i, X33 : $i]:
% 0.19/0.50         (((k7_relat_1 @ X32 @ X33) != (k1_xboole_0))
% 0.19/0.50          | (r1_xboole_0 @ (k1_relat_1 @ X32) @ X33)
% 0.19/0.50          | ~ (v1_relat_1 @ X32))),
% 0.19/0.50      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.50         | ~ (v1_relat_1 @ sk_B)
% 0.19/0.50         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.50         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['51'])).
% 0.19/0.50  thf('53', plain,
% 0.19/0.50      (![X25 : $i, X26 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ (k1_relat_1 @ X25) @ X26)
% 0.19/0.50          | ((k9_relat_1 @ X25 @ X26) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ X25))),
% 0.19/0.50      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      (((~ (v1_relat_1 @ sk_B)
% 0.19/0.50         | ((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.50  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['54', '55'])).
% 0.19/0.50  thf('57', plain,
% 0.19/0.50      (![X23 : $i, X24 : $i]:
% 0.19/0.50         (((k11_relat_1 @ X23 @ X24) = (k9_relat_1 @ X23 @ (k1_tarski @ X24)))
% 0.19/0.50          | ~ (v1_relat_1 @ X23))),
% 0.19/0.50      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.19/0.50  thf('58', plain,
% 0.19/0.50      (((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B)))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['56', '57'])).
% 0.19/0.50  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('60', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.19/0.50         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.50  thf('61', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.19/0.50         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.19/0.50      inference('split', [status(esa)], ['24'])).
% 0.19/0.50  thf('62', plain,
% 0.19/0.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.50         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.19/0.50             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.50  thf('63', plain,
% 0.19/0.50      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.19/0.50       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['62'])).
% 0.19/0.50  thf('64', plain, ($false),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '63'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
