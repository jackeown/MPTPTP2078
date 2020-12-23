%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1qGOiqLbxz

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:12 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 201 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :   26
%              Number of atoms          :  742 (1810 expanded)
%              Number of equality atoms :   37 (  97 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ X0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ X0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
        | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ X0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('38',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','45'])).

thf('47',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('49',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('50',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','45','49'])).

thf('51',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('54',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ X22 ) )
      | ( r2_hidden @ X20 @ ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','57'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('59',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('63',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['61','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['47','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1qGOiqLbxz
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.58/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.58/1.78  % Solved by: fo/fo7.sh
% 1.58/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.58/1.78  % done 2706 iterations in 1.331s
% 1.58/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.58/1.78  % SZS output start Refutation
% 1.58/1.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.58/1.78  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.58/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.58/1.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.58/1.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.58/1.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.58/1.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.58/1.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.58/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.58/1.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.58/1.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.58/1.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.58/1.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.58/1.78  thf(t95_relat_1, conjecture,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( v1_relat_1 @ B ) =>
% 1.58/1.78       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 1.58/1.78         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.58/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.58/1.78    (~( ![A:$i,B:$i]:
% 1.58/1.78        ( ( v1_relat_1 @ B ) =>
% 1.58/1.78          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 1.58/1.78            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 1.58/1.78    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 1.58/1.78  thf('0', plain,
% 1.58/1.78      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.58/1.78        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('1', plain,
% 1.58/1.78      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.58/1.78         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('split', [status(esa)], ['0'])).
% 1.58/1.78  thf('2', plain,
% 1.58/1.78      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 1.58/1.78       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.58/1.78      inference('split', [status(esa)], ['0'])).
% 1.58/1.78  thf(dt_k7_relat_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.58/1.78  thf('3', plain,
% 1.58/1.78      (![X17 : $i, X18 : $i]:
% 1.58/1.78         (~ (v1_relat_1 @ X17) | (v1_relat_1 @ (k7_relat_1 @ X17 @ X18)))),
% 1.58/1.78      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.58/1.78  thf(t87_relat_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( v1_relat_1 @ B ) =>
% 1.58/1.78       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.58/1.78  thf('4', plain,
% 1.58/1.78      (![X23 : $i, X24 : $i]:
% 1.58/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X23 @ X24)) @ X24)
% 1.58/1.78          | ~ (v1_relat_1 @ X23))),
% 1.58/1.78      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.58/1.78  thf('5', plain,
% 1.58/1.78      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.58/1.78        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('6', plain,
% 1.58/1.78      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('split', [status(esa)], ['5'])).
% 1.58/1.78  thf(symmetry_r1_xboole_0, axiom,
% 1.58/1.78    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.58/1.78  thf('7', plain,
% 1.58/1.78      (![X1 : $i, X2 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X1 @ X2) | ~ (r1_xboole_0 @ X2 @ X1))),
% 1.58/1.78      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.58/1.78  thf('8', plain,
% 1.58/1.78      (((r1_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['6', '7'])).
% 1.58/1.78  thf('9', plain,
% 1.58/1.78      (![X23 : $i, X24 : $i]:
% 1.58/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X23 @ X24)) @ X24)
% 1.58/1.78          | ~ (v1_relat_1 @ X23))),
% 1.58/1.78      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.58/1.78  thf(t63_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.58/1.78       ( r1_xboole_0 @ A @ C ) ))).
% 1.58/1.78  thf('10', plain,
% 1.58/1.78      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.58/1.78         (~ (r1_tarski @ X7 @ X8)
% 1.58/1.78          | ~ (r1_xboole_0 @ X8 @ X9)
% 1.58/1.78          | (r1_xboole_0 @ X7 @ X9))),
% 1.58/1.78      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.58/1.78  thf('11', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (~ (v1_relat_1 @ X1)
% 1.58/1.78          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 1.58/1.78          | ~ (r1_xboole_0 @ X0 @ X2))),
% 1.58/1.78      inference('sup-', [status(thm)], ['9', '10'])).
% 1.58/1.78  thf('12', plain,
% 1.58/1.78      ((![X0 : $i]:
% 1.58/1.78          ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)) @ 
% 1.58/1.78            (k1_relat_1 @ sk_B))
% 1.58/1.78           | ~ (v1_relat_1 @ X0)))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['8', '11'])).
% 1.58/1.78  thf('13', plain,
% 1.58/1.78      (![X1 : $i, X2 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X1 @ X2) | ~ (r1_xboole_0 @ X2 @ X1))),
% 1.58/1.78      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.58/1.78  thf('14', plain,
% 1.58/1.78      ((![X0 : $i]:
% 1.58/1.78          (~ (v1_relat_1 @ X0)
% 1.58/1.78           | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 1.58/1.78              (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)))))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['12', '13'])).
% 1.58/1.78  thf(t89_relat_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( v1_relat_1 @ B ) =>
% 1.58/1.78       ( r1_tarski @
% 1.58/1.78         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 1.58/1.78  thf('15', plain,
% 1.58/1.78      (![X25 : $i, X26 : $i]:
% 1.58/1.78         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X25 @ X26)) @ 
% 1.58/1.78           (k1_relat_1 @ X25))
% 1.58/1.78          | ~ (v1_relat_1 @ X25))),
% 1.58/1.78      inference('cnf', [status(esa)], [t89_relat_1])).
% 1.58/1.78  thf('16', plain,
% 1.58/1.78      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.58/1.78         (~ (r1_tarski @ X7 @ X8)
% 1.58/1.78          | ~ (r1_xboole_0 @ X8 @ X9)
% 1.58/1.78          | (r1_xboole_0 @ X7 @ X9))),
% 1.58/1.78      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.58/1.78  thf('17', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (~ (v1_relat_1 @ X0)
% 1.58/1.78          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 1.58/1.78          | ~ (r1_xboole_0 @ (k1_relat_1 @ X0) @ X2))),
% 1.58/1.78      inference('sup-', [status(thm)], ['15', '16'])).
% 1.58/1.78  thf('18', plain,
% 1.58/1.78      ((![X0 : $i, X1 : $i]:
% 1.58/1.78          (~ (v1_relat_1 @ X0)
% 1.58/1.78           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X1)) @ 
% 1.58/1.78              (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)))
% 1.58/1.78           | ~ (v1_relat_1 @ sk_B)))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['14', '17'])).
% 1.58/1.78  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('20', plain,
% 1.58/1.78      ((![X0 : $i, X1 : $i]:
% 1.58/1.78          (~ (v1_relat_1 @ X0)
% 1.58/1.78           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X1)) @ 
% 1.58/1.78              (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)))))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('demod', [status(thm)], ['18', '19'])).
% 1.58/1.78  thf(t3_xboole_0, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.58/1.78            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.58/1.78       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.58/1.78            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.58/1.78  thf('21', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 1.58/1.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.58/1.78  thf('22', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 1.58/1.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.58/1.78  thf('23', plain,
% 1.58/1.78      (![X3 : $i, X5 : $i, X6 : $i]:
% 1.58/1.78         (~ (r2_hidden @ X5 @ X3)
% 1.58/1.78          | ~ (r2_hidden @ X5 @ X6)
% 1.58/1.78          | ~ (r1_xboole_0 @ X3 @ X6))),
% 1.58/1.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.58/1.78  thf('24', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X0 @ X1)
% 1.58/1.78          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.58/1.78          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 1.58/1.78      inference('sup-', [status(thm)], ['22', '23'])).
% 1.58/1.78  thf('25', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X0 @ X1)
% 1.58/1.78          | ~ (r1_xboole_0 @ X0 @ X0)
% 1.58/1.78          | (r1_xboole_0 @ X0 @ X1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['21', '24'])).
% 1.58/1.78  thf('26', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.58/1.78      inference('simplify', [status(thm)], ['25'])).
% 1.58/1.78  thf('27', plain,
% 1.58/1.78      ((![X0 : $i]:
% 1.58/1.78          (~ (v1_relat_1 @ sk_B)
% 1.58/1.78           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ X0)))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['20', '26'])).
% 1.58/1.78  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('29', plain,
% 1.58/1.78      ((![X0 : $i]:
% 1.58/1.78          (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ X0))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('demod', [status(thm)], ['27', '28'])).
% 1.58/1.78  thf(t69_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.58/1.78       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.58/1.78  thf('30', plain,
% 1.58/1.78      (![X10 : $i, X11 : $i]:
% 1.58/1.78         (~ (r1_xboole_0 @ X10 @ X11)
% 1.58/1.78          | ~ (r1_tarski @ X10 @ X11)
% 1.58/1.78          | (v1_xboole_0 @ X10))),
% 1.58/1.78      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.58/1.78  thf('31', plain,
% 1.58/1.78      ((![X0 : $i]:
% 1.58/1.78          ((v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.58/1.78           | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ X0)))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['29', '30'])).
% 1.58/1.78  thf('32', plain,
% 1.58/1.78      (((~ (v1_relat_1 @ sk_B)
% 1.58/1.78         | (v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['4', '31'])).
% 1.58/1.78  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('34', plain,
% 1.58/1.78      (((v1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('demod', [status(thm)], ['32', '33'])).
% 1.58/1.78  thf(l13_xboole_0, axiom,
% 1.58/1.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.58/1.78  thf('35', plain,
% 1.58/1.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.58/1.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.58/1.78  thf('36', plain,
% 1.58/1.78      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0)))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['34', '35'])).
% 1.58/1.78  thf(t64_relat_1, axiom,
% 1.58/1.78    (![A:$i]:
% 1.58/1.78     ( ( v1_relat_1 @ A ) =>
% 1.58/1.78       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.58/1.78           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.58/1.78         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.58/1.78  thf('37', plain,
% 1.58/1.78      (![X19 : $i]:
% 1.58/1.78         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 1.58/1.78          | ((X19) = (k1_xboole_0))
% 1.58/1.78          | ~ (v1_relat_1 @ X19))),
% 1.58/1.78      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.58/1.78  thf('38', plain,
% 1.58/1.78      (((((k1_xboole_0) != (k1_xboole_0))
% 1.58/1.78         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 1.58/1.78         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['36', '37'])).
% 1.58/1.78  thf('39', plain,
% 1.58/1.78      (((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.58/1.78         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('simplify', [status(thm)], ['38'])).
% 1.58/1.78  thf('40', plain,
% 1.58/1.78      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['3', '39'])).
% 1.58/1.78  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('42', plain,
% 1.58/1.78      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 1.58/1.78         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('demod', [status(thm)], ['40', '41'])).
% 1.58/1.78  thf('43', plain,
% 1.58/1.78      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 1.58/1.78         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 1.58/1.78      inference('split', [status(esa)], ['0'])).
% 1.58/1.78  thf('44', plain,
% 1.58/1.78      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.58/1.78         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 1.58/1.78             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['42', '43'])).
% 1.58/1.78  thf('45', plain,
% 1.58/1.78      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 1.58/1.78       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.58/1.78      inference('simplify', [status(thm)], ['44'])).
% 1.58/1.78  thf('46', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.58/1.78      inference('sat_resolution*', [status(thm)], ['2', '45'])).
% 1.58/1.78  thf('47', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 1.58/1.78  thf('48', plain,
% 1.58/1.78      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 1.58/1.78         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 1.58/1.78      inference('split', [status(esa)], ['5'])).
% 1.58/1.78  thf('49', plain,
% 1.58/1.78      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 1.58/1.78       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.58/1.78      inference('split', [status(esa)], ['5'])).
% 1.58/1.78  thf('50', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.58/1.78      inference('sat_resolution*', [status(thm)], ['2', '45', '49'])).
% 1.58/1.78  thf('51', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['48', '50'])).
% 1.58/1.78  thf('52', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 1.58/1.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.58/1.78  thf('53', plain,
% 1.58/1.78      (![X3 : $i, X4 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 1.58/1.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.58/1.78  thf(t86_relat_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( v1_relat_1 @ C ) =>
% 1.58/1.78       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 1.58/1.78         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 1.58/1.78  thf('54', plain,
% 1.58/1.78      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.58/1.78         (~ (r2_hidden @ X20 @ X21)
% 1.58/1.78          | ~ (r2_hidden @ X20 @ (k1_relat_1 @ X22))
% 1.58/1.78          | (r2_hidden @ X20 @ (k1_relat_1 @ (k7_relat_1 @ X22 @ X21)))
% 1.58/1.78          | ~ (v1_relat_1 @ X22))),
% 1.58/1.78      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.58/1.78  thf('55', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 1.58/1.78          | ~ (v1_relat_1 @ X0)
% 1.58/1.78          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 1.58/1.78             (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 1.58/1.78          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 1.58/1.78      inference('sup-', [status(thm)], ['53', '54'])).
% 1.58/1.78  thf('56', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 1.58/1.78          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 1.58/1.78             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.58/1.78          | ~ (v1_relat_1 @ X1)
% 1.58/1.78          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 1.58/1.78      inference('sup-', [status(thm)], ['52', '55'])).
% 1.58/1.78  thf('57', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (~ (v1_relat_1 @ X1)
% 1.58/1.78          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 1.58/1.78             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.58/1.78          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 1.58/1.78      inference('simplify', [status(thm)], ['56'])).
% 1.58/1.78  thf('58', plain,
% 1.58/1.78      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B)) @ 
% 1.58/1.78         (k1_relat_1 @ k1_xboole_0))
% 1.58/1.78        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 1.58/1.78        | ~ (v1_relat_1 @ sk_B))),
% 1.58/1.78      inference('sup+', [status(thm)], ['51', '57'])).
% 1.58/1.78  thf(t60_relat_1, axiom,
% 1.58/1.78    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.58/1.78     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.58/1.78  thf('59', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.58/1.78      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.58/1.78  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('61', plain,
% 1.58/1.78      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B)) @ k1_xboole_0)
% 1.58/1.78        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.58/1.78      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.58/1.78  thf(t113_zfmisc_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.58/1.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.58/1.78  thf('62', plain,
% 1.58/1.78      (![X13 : $i, X14 : $i]:
% 1.58/1.78         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 1.58/1.78          | ((X14) != (k1_xboole_0)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.58/1.78  thf('63', plain,
% 1.58/1.78      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 1.58/1.78      inference('simplify', [status(thm)], ['62'])).
% 1.58/1.78  thf(t152_zfmisc_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.58/1.78  thf('64', plain,
% 1.58/1.78      (![X15 : $i, X16 : $i]: ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X15 @ X16))),
% 1.58/1.78      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 1.58/1.78  thf('65', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.58/1.78      inference('sup-', [status(thm)], ['63', '64'])).
% 1.58/1.78  thf('66', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 1.58/1.78      inference('clc', [status(thm)], ['61', '65'])).
% 1.58/1.78  thf('67', plain, ($false), inference('demod', [status(thm)], ['47', '66'])).
% 1.58/1.78  
% 1.58/1.78  % SZS output end Refutation
% 1.58/1.78  
% 1.58/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
