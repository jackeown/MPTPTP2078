%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iG0H03R25F

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:22 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 131 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  747 (1887 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t171_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) )
            <=> ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                & ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) )
              <=> ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) )
                  & ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t171_funct_1])).

thf('0',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X8 @ X9 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        | ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('20',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X15 @ X14 ) @ X16 )
      | ( r1_tarski @ X14 @ ( k10_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('31',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('39',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k9_relat_1 @ X7 @ X5 ) @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( ( k2_xboole_0 @ ( k9_relat_1 @ X0 @ sk_C ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
          = ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('49',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C ) @ X1 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('56',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','19','35','36','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iG0H03R25F
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 193 iterations in 0.162s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.62  thf(t171_funct_1, conjecture,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62           ( ![C:$i]:
% 0.38/0.62             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.38/0.62               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.62                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i]:
% 0.38/0.62        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62          ( ![B:$i]:
% 0.38/0.62            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62              ( ![C:$i]:
% 0.38/0.62                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.38/0.62                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.62                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.38/0.62        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.38/0.62       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('split', [status(esa)], ['0'])).
% 0.38/0.62  thf(t167_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ B ) =>
% 0.38/0.62       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X8 : $i, X9 : $i]:
% 0.38/0.62         ((r1_tarski @ (k10_relat_1 @ X8 @ X9) @ (k1_relat_1 @ X8))
% 0.38/0.62          | ~ (v1_relat_1 @ X8))),
% 0.38/0.62      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.38/0.62  thf(t182_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( v1_relat_1 @ B ) =>
% 0.38/0.62           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.38/0.62             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X10 : $i, X11 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X10)
% 0.38/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 0.38/0.62              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 0.38/0.62          | ~ (v1_relat_1 @ X11))),
% 0.38/0.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('split', [status(esa)], ['0'])).
% 0.38/0.62  thf(t12_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X3 : $i, X4 : $i]:
% 0.38/0.62         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      ((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.38/0.62          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.62  thf(t11_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          (~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)
% 0.38/0.62           | (r1_tarski @ sk_C @ X0)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 0.38/0.62           | ~ (v1_relat_1 @ sk_A)
% 0.38/0.62           | ~ (v1_relat_1 @ sk_B)
% 0.38/0.62           | (r1_tarski @ sk_C @ X0)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['3', '8'])).
% 0.38/0.62  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 0.38/0.62           | (r1_tarski @ sk_C @ X0)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (((~ (v1_relat_1 @ sk_A) | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['2', '12'])).
% 0.38/0.62  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.38/0.62        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.38/0.62        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.38/0.62         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.38/0.62      inference('split', [status(esa)], ['16'])).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.38/0.62       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['15', '17'])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.38/0.62       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.38/0.62       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.38/0.62      inference('split', [status(esa)], ['16'])).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.38/0.62        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.38/0.62         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.38/0.62      inference('split', [status(esa)], ['20'])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.38/0.62      inference('split', [status(esa)], ['0'])).
% 0.38/0.62  thf(t163_funct_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.62       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.38/0.62           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.38/0.62         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.38/0.62          | ~ (r1_tarski @ (k9_relat_1 @ X15 @ X14) @ X16)
% 0.38/0.62          | (r1_tarski @ X14 @ (k10_relat_1 @ X15 @ X16))
% 0.38/0.62          | ~ (v1_funct_1 @ X15)
% 0.38/0.62          | ~ (v1_relat_1 @ X15))),
% 0.38/0.62      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          (~ (v1_relat_1 @ sk_A)
% 0.38/0.62           | ~ (v1_funct_1 @ sk_A)
% 0.38/0.62           | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.38/0.62           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('26', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.38/0.62           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.38/0.62      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.38/0.62  thf('28', plain,
% 0.38/0.62      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) & 
% 0.38/0.62             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['21', '27'])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X10 : $i, X11 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X10)
% 0.38/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 0.38/0.62              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 0.38/0.62          | ~ (v1_relat_1 @ X11))),
% 0.38/0.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.38/0.62         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('split', [status(esa)], ['16'])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.38/0.62         | ~ (v1_relat_1 @ sk_A)
% 0.38/0.62         | ~ (v1_relat_1 @ sk_B)))
% 0.38/0.62         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.62  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      ((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.38/0.62         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.38/0.62       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.38/0.62       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['28', '34'])).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.38/0.62       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.38/0.62      inference('split', [status(esa)], ['20'])).
% 0.38/0.62  thf(t145_funct_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X12 : $i, X13 : $i]:
% 0.38/0.62         ((r1_tarski @ (k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X13)) @ X13)
% 0.38/0.62          | ~ (v1_funct_1 @ X12)
% 0.38/0.62          | ~ (v1_relat_1 @ X12))),
% 0.38/0.62      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      (![X10 : $i, X11 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X10)
% 0.38/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 0.38/0.62              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 0.38/0.62          | ~ (v1_relat_1 @ X11))),
% 0.38/0.62      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('split', [status(esa)], ['0'])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      ((((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.38/0.62         | ~ (v1_relat_1 @ sk_A)
% 0.38/0.62         | ~ (v1_relat_1 @ sk_B)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup+', [status(thm)], ['38', '39'])).
% 0.38/0.62  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('43', plain,
% 0.38/0.62      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.38/0.62  thf(t156_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ C ) =>
% 0.38/0.62       ( ( r1_tarski @ A @ B ) =>
% 0.38/0.62         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.62  thf('44', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.62         (~ (r1_tarski @ X5 @ X6)
% 0.38/0.62          | ~ (v1_relat_1 @ X7)
% 0.38/0.62          | (r1_tarski @ (k9_relat_1 @ X7 @ X5) @ (k9_relat_1 @ X7 @ X6)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.38/0.62  thf('45', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_C) @ 
% 0.38/0.62            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.38/0.62           | ~ (v1_relat_1 @ X0)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.62  thf('46', plain,
% 0.38/0.62      (![X3 : $i, X4 : $i]:
% 0.38/0.62         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.62  thf('47', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          (~ (v1_relat_1 @ X0)
% 0.38/0.62           | ((k2_xboole_0 @ (k9_relat_1 @ X0 @ sk_C) @ 
% 0.38/0.62               (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.38/0.62               = (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.62  thf('48', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.38/0.62  thf('49', plain,
% 0.38/0.62      ((![X0 : $i, X1 : $i]:
% 0.38/0.62          (~ (r1_tarski @ 
% 0.38/0.62              (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.38/0.62              X1)
% 0.38/0.62           | ~ (v1_relat_1 @ X0)
% 0.38/0.62           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_C) @ X1)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.62  thf('50', plain,
% 0.38/0.62      (((~ (v1_relat_1 @ sk_A)
% 0.38/0.62         | ~ (v1_funct_1 @ sk_A)
% 0.38/0.62         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.38/0.62         | ~ (v1_relat_1 @ sk_A)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['37', '49'])).
% 0.38/0.62  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('52', plain, ((v1_funct_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('54', plain,
% 0.38/0.62      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.38/0.62         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.38/0.62      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.38/0.62         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.38/0.62      inference('split', [status(esa)], ['16'])).
% 0.38/0.62  thf('56', plain,
% 0.38/0.62      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.38/0.62       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.62  thf('57', plain, ($false),
% 0.38/0.62      inference('sat_resolution*', [status(thm)],
% 0.38/0.62                ['1', '18', '19', '35', '36', '56'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
