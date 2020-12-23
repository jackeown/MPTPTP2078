%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rgh5c9Va2X

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 141 expanded)
%              Number of leaves         :   26 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  584 ( 903 expanded)
%              Number of equality atoms :   48 (  84 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X31 @ X32 ) )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ X22 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('8',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','9','10'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('24',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('32',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('37',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('60',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['30','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['62','63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rgh5c9Va2X
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:25:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 149 iterations in 0.104s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.57  thf(dt_k5_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.22/0.57       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      (![X25 : $i, X26 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X25)
% 0.22/0.57          | ~ (v1_relat_1 @ X26)
% 0.22/0.57          | (v1_relat_1 @ (k5_relat_1 @ X25 @ X26)))),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.57  thf(t60_relat_1, axiom,
% 0.22/0.57    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.57     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.57  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.57  thf(t47_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( v1_relat_1 @ B ) =>
% 0.22/0.57           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.22/0.57             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X31 : $i, X32 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X31)
% 0.22/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X31 @ X32)) = (k2_relat_1 @ X32))
% 0.22/0.57          | ~ (r1_tarski @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X31))
% 0.22/0.57          | ~ (v1_relat_1 @ X32))),
% 0.22/0.57      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.57              = (k2_relat_1 @ k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.57  thf('4', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.57  thf(d1_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) <=>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.57              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X22 : $i]: ((v1_relat_1 @ X22) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 0.22/0.57      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.22/0.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.57  thf('6', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.57  thf(t55_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.57         (~ (r1_xboole_0 @ (k2_tarski @ X17 @ X18) @ X19)
% 0.22/0.57          | ~ (r2_hidden @ X17 @ X19))),
% 0.22/0.57      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.22/0.57  thf('8', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.57  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.22/0.57  thf('10', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['3', '4', '9', '10'])).
% 0.22/0.57  thf(fc9_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.22/0.57       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X28 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ (k2_relat_1 @ X28))
% 0.22/0.57          | ~ (v1_relat_1 @ X28)
% 0.22/0.57          | (v1_xboole_0 @ X28))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.57  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '15'])).
% 0.22/0.57  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.57  thf(l13_xboole_0, axiom,
% 0.22/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.57  thf(t62_relat_1, conjecture,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.57         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i]:
% 0.22/0.57        ( ( v1_relat_1 @ A ) =>
% 0.22/0.57          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.22/0.57            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.22/0.57        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['24'])).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      ((![X0 : $i]:
% 0.22/0.57          (((X0) != (k1_xboole_0))
% 0.22/0.57           | ~ (v1_xboole_0 @ X0)
% 0.22/0.57           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.22/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['23', '25'])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.22/0.57         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.57  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.57      inference('simplify_reflect+', [status(thm)], ['27', '28'])).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      ((![X0 : $i]:
% 0.22/0.57          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['20', '29'])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X25 : $i, X26 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X25)
% 0.22/0.57          | ~ (v1_relat_1 @ X26)
% 0.22/0.57          | (v1_relat_1 @ (k5_relat_1 @ X25 @ X26)))),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.22/0.57  thf('32', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.57  thf(t46_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( v1_relat_1 @ B ) =>
% 0.22/0.57           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.57             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      (![X29 : $i, X30 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X29)
% 0.22/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X30 @ X29)) = (k1_relat_1 @ X30))
% 0.22/0.57          | ~ (r1_tarski @ (k2_relat_1 @ X30) @ (k1_relat_1 @ X29))
% 0.22/0.57          | ~ (v1_relat_1 @ X30))),
% 0.22/0.57      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.57          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.57              = (k1_relat_1 @ k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.57  thf('35', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.57  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.22/0.57  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.22/0.57  thf(fc8_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.22/0.57       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      (![X27 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ (k1_relat_1 @ X27))
% 0.22/0.57          | ~ (v1_relat_1 @ X27)
% 0.22/0.57          | (v1_xboole_0 @ X27))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.22/0.57  thf('40', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.57  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.57          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['31', '42'])).
% 0.22/0.57  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.57  thf('46', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.57  thf('48', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.57  thf('49', plain,
% 0.22/0.57      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['24'])).
% 0.22/0.57  thf('50', plain,
% 0.22/0.57      ((![X0 : $i]:
% 0.22/0.57          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.57  thf('51', plain,
% 0.22/0.57      ((![X0 : $i, X1 : $i]:
% 0.22/0.57          (((X0) != (k1_xboole_0))
% 0.22/0.57           | ~ (v1_xboole_0 @ X0)
% 0.22/0.57           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.22/0.57           | ~ (v1_xboole_0 @ X1)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['47', '50'])).
% 0.22/0.57  thf('52', plain,
% 0.22/0.57      ((![X1 : $i]:
% 0.22/0.57          (~ (v1_xboole_0 @ X1)
% 0.22/0.57           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.22/0.57           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.57  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf('54', plain,
% 0.22/0.57      ((![X1 : $i]:
% 0.22/0.57          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.22/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('simplify_reflect+', [status(thm)], ['52', '53'])).
% 0.22/0.57  thf('55', plain,
% 0.22/0.57      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.22/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['46', '54'])).
% 0.22/0.57  thf('56', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf('58', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.22/0.57  thf('59', plain,
% 0.22/0.57      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.22/0.57       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.57      inference('split', [status(esa)], ['24'])).
% 0.22/0.57  thf('60', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.57      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.22/0.57  thf('61', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.57      inference('simpl_trail', [status(thm)], ['30', '60'])).
% 0.22/0.57  thf('62', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['19', '61'])).
% 0.22/0.57  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf('65', plain, ($false),
% 0.22/0.57      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
