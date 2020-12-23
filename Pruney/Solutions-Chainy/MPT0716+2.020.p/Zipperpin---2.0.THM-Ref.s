%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6ZyfA2oCUj

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 172 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :   19
%              Number of atoms          :  950 (2539 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('3',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('14',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
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

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X21 @ X20 ) @ X22 )
      | ( r1_tarski @ X20 @ ( k10_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('25',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('36',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('38',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
        = sk_C )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X23 @ X24 ) )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('48',plain,
    ( ( ( sk_C
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('51',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( sk_C != sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','53','54','55'])).

thf('57',plain,
    ( ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['31','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('69',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','13','29','30','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6ZyfA2oCUj
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:57:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 84 iterations in 0.075s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(t171_funct_1, conjecture,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.21/0.55               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.55                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i]:
% 0.21/0.55        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55          ( ![B:$i]:
% 0.21/0.55            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55              ( ![C:$i]:
% 0.21/0.55                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.21/0.55                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.55                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.21/0.55        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.21/0.55       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf(t44_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( v1_relat_1 @ B ) =>
% 0.21/0.55           ( r1_tarski @
% 0.21/0.55             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X14)
% 0.21/0.55          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X15 @ X14)) @ 
% 0.21/0.55             (k1_relat_1 @ X15))
% 0.21/0.55          | ~ (v1_relat_1 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.21/0.55         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf(t1_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.55       ( r1_tarski @ A @ C ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.55          | (r1_tarski @ X0 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          ((r1_tarski @ sk_C @ X0)
% 0.21/0.55           | ~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)))
% 0.21/0.55         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (((~ (v1_relat_1 @ sk_A)
% 0.21/0.55         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.55         | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 0.21/0.55         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.55  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.21/0.55         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.21/0.55        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.21/0.55        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.21/0.55         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.21/0.55      inference('split', [status(esa)], ['10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.21/0.55       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.21/0.55       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.21/0.55       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.21/0.55      inference('split', [status(esa)], ['10'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.21/0.55        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.21/0.56         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.21/0.56      inference('split', [status(esa)], ['14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf(t163_funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.56       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.56           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.21/0.56         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 0.21/0.56          | ~ (r1_tarski @ (k9_relat_1 @ X21 @ X20) @ X22)
% 0.21/0.56          | (r1_tarski @ X20 @ (k10_relat_1 @ X21 @ X22))
% 0.21/0.56          | ~ (v1_funct_1 @ X21)
% 0.21/0.56          | ~ (v1_relat_1 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (~ (v1_relat_1 @ sk_A)
% 0.21/0.56           | ~ (v1_funct_1 @ sk_A)
% 0.21/0.56           | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.21/0.56           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('20', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.21/0.56           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) & 
% 0.21/0.56             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '21'])).
% 0.21/0.56  thf(t182_relat_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( v1_relat_1 @ B ) =>
% 0.21/0.56           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.56             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X12)
% 0.21/0.56          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.21/0.56              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.21/0.56          | ~ (v1_relat_1 @ X13))),
% 0.21/0.56      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.21/0.56         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('split', [status(esa)], ['10'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.21/0.56         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.56         | ~ (v1_relat_1 @ sk_B)))
% 0.21/0.56         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.21/0.56         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.21/0.56       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.21/0.56       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '28'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.21/0.56       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.21/0.56      inference('split', [status(esa)], ['14'])).
% 0.21/0.56  thf(t148_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]:
% 0.21/0.56         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.21/0.56          | ~ (v1_relat_1 @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.56  thf(fc8_funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.56       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.21/0.56         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (v1_funct_1 @ X18)
% 0.21/0.56          | ~ (v1_relat_1 @ X18)
% 0.21/0.56          | (v1_funct_1 @ (k7_relat_1 @ X18 @ X19)))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.21/0.56  thf(dt_k7_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X5 : $i, X6 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.56  thf(t112_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( v1_relat_1 @ C ) =>
% 0.21/0.56           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.56             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X7)
% 0.21/0.56          | ((k7_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.21/0.56              = (k5_relat_1 @ (k7_relat_1 @ X8 @ X9) @ X7))
% 0.21/0.56          | ~ (v1_relat_1 @ X8))),
% 0.21/0.56      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.21/0.56  thf(dt_k5_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.56       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X3)
% 0.21/0.56          | ~ (v1_relat_1 @ X4)
% 0.21/0.56          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf(t91_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.56         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.21/0.56          | ((k1_relat_1 @ (k7_relat_1 @ X17 @ X16)) = (X16))
% 0.21/0.56          | ~ (v1_relat_1 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 0.21/0.56         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.21/0.56             = (sk_C))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (((~ (v1_relat_1 @ sk_B)
% 0.21/0.56         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.56         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.21/0.56             = (sk_C))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['35', '38'])).
% 0.21/0.56  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      ((((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.21/0.56          = (sk_C)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.21/0.56           = (sk_C))
% 0.21/0.56         | ~ (v1_relat_1 @ sk_A)
% 0.21/0.56         | ~ (v1_relat_1 @ sk_B)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['34', '42'])).
% 0.21/0.56  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.21/0.56          = (sk_C)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.21/0.56  thf(t27_funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.21/0.56             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X23)
% 0.21/0.56          | ~ (v1_funct_1 @ X23)
% 0.21/0.56          | (r1_tarski @ (k2_relat_1 @ X23) @ (k1_relat_1 @ X24))
% 0.21/0.56          | ((k1_relat_1 @ (k5_relat_1 @ X23 @ X24)) != (k1_relat_1 @ X23))
% 0.21/0.56          | ~ (v1_funct_1 @ X24)
% 0.21/0.56          | ~ (v1_relat_1 @ X24))),
% 0.21/0.56      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (((((sk_C) != (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 0.21/0.56         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.56         | ~ (v1_funct_1 @ sk_B)
% 0.21/0.56         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.21/0.56            (k1_relat_1 @ sk_B))
% 0.21/0.56         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.21/0.56         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.21/0.56          | ((k1_relat_1 @ (k7_relat_1 @ X17 @ X16)) = (X16))
% 0.21/0.56          | ~ (v1_relat_1 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (((~ (v1_relat_1 @ sk_A)
% 0.21/0.56         | ((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) = (sk_C)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.56  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      (((((sk_C) != (sk_C))
% 0.21/0.56         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.21/0.56            (k1_relat_1 @ sk_B))
% 0.21/0.56         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.21/0.56         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['48', '53', '54', '55'])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (((~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.21/0.56         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 0.21/0.56         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.21/0.56            (k1_relat_1 @ sk_B))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (((~ (v1_relat_1 @ sk_A)
% 0.21/0.56         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.21/0.56            (k1_relat_1 @ sk_B))
% 0.21/0.56         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '57'])).
% 0.21/0.56  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      ((((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.21/0.56          (k1_relat_1 @ sk_B))
% 0.21/0.56         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      (((~ (v1_relat_1 @ sk_A)
% 0.21/0.56         | ~ (v1_funct_1 @ sk_A)
% 0.21/0.56         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.21/0.56            (k1_relat_1 @ sk_B))))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['32', '60'])).
% 0.21/0.56  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('63', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 0.21/0.56         (k1_relat_1 @ sk_B)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.21/0.56         | ~ (v1_relat_1 @ sk_A)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('sup+', [status(thm)], ['31', '64'])).
% 0.21/0.56  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.21/0.56         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.21/0.56      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.21/0.56         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.21/0.56      inference('split', [status(esa)], ['10'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.21/0.56       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.56  thf('70', plain, ($false),
% 0.21/0.56      inference('sat_resolution*', [status(thm)],
% 0.21/0.56                ['1', '12', '13', '29', '30', '69'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
