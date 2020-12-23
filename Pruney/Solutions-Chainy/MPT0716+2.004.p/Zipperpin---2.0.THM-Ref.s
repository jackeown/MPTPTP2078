%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WuqXZE6d8z

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:19 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 241 expanded)
%              Number of leaves         :   26 (  76 expanded)
%              Depth                    :   24
%              Number of atoms          : 1068 (3538 expanded)
%              Number of equality atoms :   25 (  46 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
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

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
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

thf('5',plain,(
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

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('10',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
        = sk_C ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
        = sk_C )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

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

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ( r1_tarski @ ( k2_relat_1 @ X28 ) @ ( k1_relat_1 @ X29 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X28 @ X29 ) )
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('20',plain,
    ( ( ( sk_C
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( sk_C
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('25',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('27',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( sk_C
        = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_C
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( sk_C != sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','38'])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['2','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('55',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('57',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ ( k1_relat_1 @ X26 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X26 @ X25 ) @ X27 )
      | ( r1_tarski @ X25 @ ( k10_relat_1 @ X26 @ X27 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['51'])).

thf('65',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('71',plain,
    ( ( sk_C
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('72',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf('73',plain,
    ( ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['51'])).

thf('77',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','53','54','69','70','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WuqXZE6d8z
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:29:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.30/1.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.30/1.49  % Solved by: fo/fo7.sh
% 1.30/1.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.49  % done 805 iterations in 1.032s
% 1.30/1.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.30/1.49  % SZS output start Refutation
% 1.30/1.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.30/1.49  thf(sk_C_type, type, sk_C: $i).
% 1.30/1.49  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.30/1.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.30/1.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.30/1.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.30/1.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.30/1.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.30/1.49  thf(sk_B_type, type, sk_B: $i).
% 1.30/1.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.30/1.49  thf(t171_funct_1, conjecture,
% 1.30/1.49    (![A:$i]:
% 1.30/1.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.49       ( ![B:$i]:
% 1.30/1.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.30/1.49           ( ![C:$i]:
% 1.30/1.49             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 1.30/1.49               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 1.30/1.49                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 1.30/1.49  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.49    (~( ![A:$i]:
% 1.30/1.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.49          ( ![B:$i]:
% 1.30/1.49            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.30/1.49              ( ![C:$i]:
% 1.30/1.49                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 1.30/1.49                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 1.30/1.49                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 1.30/1.49    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 1.30/1.49  thf('0', plain,
% 1.30/1.49      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 1.30/1.49        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('1', plain,
% 1.30/1.49      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.30/1.49       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 1.30/1.49      inference('split', [status(esa)], ['0'])).
% 1.30/1.49  thf(t148_relat_1, axiom,
% 1.30/1.49    (![A:$i,B:$i]:
% 1.30/1.49     ( ( v1_relat_1 @ B ) =>
% 1.30/1.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.30/1.49  thf('2', plain,
% 1.30/1.49      (![X10 : $i, X11 : $i]:
% 1.30/1.49         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 1.30/1.49          | ~ (v1_relat_1 @ X10))),
% 1.30/1.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.30/1.49  thf(fc8_funct_1, axiom,
% 1.30/1.49    (![A:$i,B:$i]:
% 1.30/1.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.49       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 1.30/1.49         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 1.30/1.49  thf('3', plain,
% 1.30/1.49      (![X23 : $i, X24 : $i]:
% 1.30/1.49         (~ (v1_funct_1 @ X23)
% 1.30/1.49          | ~ (v1_relat_1 @ X23)
% 1.30/1.49          | (v1_funct_1 @ (k7_relat_1 @ X23 @ X24)))),
% 1.30/1.49      inference('cnf', [status(esa)], [fc8_funct_1])).
% 1.30/1.49  thf(dt_k7_relat_1, axiom,
% 1.30/1.49    (![A:$i,B:$i]:
% 1.30/1.49     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.30/1.49  thf('4', plain,
% 1.30/1.49      (![X5 : $i, X6 : $i]:
% 1.30/1.49         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 1.30/1.49      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.30/1.49  thf(t112_relat_1, axiom,
% 1.30/1.49    (![A:$i,B:$i]:
% 1.30/1.49     ( ( v1_relat_1 @ B ) =>
% 1.30/1.49       ( ![C:$i]:
% 1.30/1.49         ( ( v1_relat_1 @ C ) =>
% 1.30/1.49           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 1.30/1.49             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 1.30/1.49  thf('5', plain,
% 1.30/1.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.30/1.49         (~ (v1_relat_1 @ X7)
% 1.30/1.49          | ((k7_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 1.30/1.49              = (k5_relat_1 @ (k7_relat_1 @ X8 @ X9) @ X7))
% 1.30/1.49          | ~ (v1_relat_1 @ X8))),
% 1.30/1.49      inference('cnf', [status(esa)], [t112_relat_1])).
% 1.30/1.49  thf(dt_k5_relat_1, axiom,
% 1.30/1.49    (![A:$i,B:$i]:
% 1.30/1.49     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.30/1.49       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.30/1.49  thf('6', plain,
% 1.30/1.49      (![X3 : $i, X4 : $i]:
% 1.30/1.49         (~ (v1_relat_1 @ X3)
% 1.30/1.49          | ~ (v1_relat_1 @ X4)
% 1.30/1.49          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 1.30/1.49      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.30/1.49  thf('7', plain,
% 1.30/1.49      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 1.30/1.49        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('8', plain,
% 1.30/1.49      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('split', [status(esa)], ['7'])).
% 1.30/1.49  thf(t91_relat_1, axiom,
% 1.30/1.49    (![A:$i,B:$i]:
% 1.30/1.49     ( ( v1_relat_1 @ B ) =>
% 1.30/1.49       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.30/1.49         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.30/1.49  thf('9', plain,
% 1.30/1.49      (![X20 : $i, X21 : $i]:
% 1.30/1.49         (~ (r1_tarski @ X20 @ (k1_relat_1 @ X21))
% 1.30/1.49          | ((k1_relat_1 @ (k7_relat_1 @ X21 @ X20)) = (X20))
% 1.30/1.49          | ~ (v1_relat_1 @ X21))),
% 1.30/1.49      inference('cnf', [status(esa)], [t91_relat_1])).
% 1.30/1.49  thf('10', plain,
% 1.30/1.49      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))
% 1.30/1.49         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 1.30/1.49             = (sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['8', '9'])).
% 1.30/1.49  thf('11', plain,
% 1.30/1.49      (((~ (v1_relat_1 @ sk_B)
% 1.30/1.49         | ~ (v1_relat_1 @ sk_A)
% 1.30/1.49         | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 1.30/1.49             = (sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['6', '10'])).
% 1.30/1.49  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('14', plain,
% 1.30/1.49      ((((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 1.30/1.49          = (sk_C)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.30/1.49  thf('15', plain,
% 1.30/1.49      (((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 1.30/1.49           = (sk_C))
% 1.30/1.49         | ~ (v1_relat_1 @ sk_A)
% 1.30/1.49         | ~ (v1_relat_1 @ sk_B)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup+', [status(thm)], ['5', '14'])).
% 1.30/1.49  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('18', plain,
% 1.30/1.49      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 1.30/1.49          = (sk_C)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.30/1.49  thf(t27_funct_1, axiom,
% 1.30/1.49    (![A:$i]:
% 1.30/1.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.49       ( ![B:$i]:
% 1.30/1.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.30/1.49           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 1.30/1.49             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 1.30/1.49  thf('19', plain,
% 1.30/1.49      (![X28 : $i, X29 : $i]:
% 1.30/1.49         (~ (v1_relat_1 @ X28)
% 1.30/1.49          | ~ (v1_funct_1 @ X28)
% 1.30/1.49          | (r1_tarski @ (k2_relat_1 @ X28) @ (k1_relat_1 @ X29))
% 1.30/1.49          | ((k1_relat_1 @ (k5_relat_1 @ X28 @ X29)) != (k1_relat_1 @ X28))
% 1.30/1.49          | ~ (v1_funct_1 @ X29)
% 1.30/1.49          | ~ (v1_relat_1 @ X29))),
% 1.30/1.49      inference('cnf', [status(esa)], [t27_funct_1])).
% 1.30/1.49  thf('20', plain,
% 1.30/1.49      (((((sk_C) != (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 1.30/1.49         | ~ (v1_relat_1 @ sk_B)
% 1.30/1.49         | ~ (v1_funct_1 @ sk_B)
% 1.30/1.49         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 1.30/1.49            (k1_relat_1 @ sk_B))
% 1.30/1.49         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 1.30/1.49         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['18', '19'])).
% 1.30/1.49  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('23', plain,
% 1.30/1.49      (((((sk_C) != (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 1.30/1.49         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 1.30/1.49            (k1_relat_1 @ sk_B))
% 1.30/1.49         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 1.30/1.49         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.30/1.49  thf('24', plain,
% 1.30/1.49      (![X5 : $i, X6 : $i]:
% 1.30/1.49         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 1.30/1.49      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.30/1.49  thf('25', plain,
% 1.30/1.49      ((((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B))
% 1.30/1.49          = (sk_C)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.30/1.49  thf(t44_relat_1, axiom,
% 1.30/1.49    (![A:$i]:
% 1.30/1.49     ( ( v1_relat_1 @ A ) =>
% 1.30/1.49       ( ![B:$i]:
% 1.30/1.49         ( ( v1_relat_1 @ B ) =>
% 1.30/1.49           ( r1_tarski @
% 1.30/1.49             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.30/1.49  thf('26', plain,
% 1.30/1.49      (![X14 : $i, X15 : $i]:
% 1.30/1.49         (~ (v1_relat_1 @ X14)
% 1.30/1.49          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X15 @ X14)) @ 
% 1.30/1.49             (k1_relat_1 @ X15))
% 1.30/1.49          | ~ (v1_relat_1 @ X15))),
% 1.30/1.49      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.30/1.49  thf('27', plain,
% 1.30/1.49      ((((r1_tarski @ sk_C @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 1.30/1.49         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 1.30/1.49         | ~ (v1_relat_1 @ sk_B)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup+', [status(thm)], ['25', '26'])).
% 1.30/1.49  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('29', plain,
% 1.30/1.49      ((((r1_tarski @ sk_C @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 1.30/1.49         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['27', '28'])).
% 1.30/1.49  thf('30', plain,
% 1.30/1.49      (((~ (v1_relat_1 @ sk_A)
% 1.30/1.49         | (r1_tarski @ sk_C @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['24', '29'])).
% 1.30/1.49  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('32', plain,
% 1.30/1.49      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['30', '31'])).
% 1.30/1.49  thf(t87_relat_1, axiom,
% 1.30/1.49    (![A:$i,B:$i]:
% 1.30/1.49     ( ( v1_relat_1 @ B ) =>
% 1.30/1.49       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 1.30/1.49  thf('33', plain,
% 1.30/1.49      (![X16 : $i, X17 : $i]:
% 1.30/1.49         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X16 @ X17)) @ X17)
% 1.30/1.49          | ~ (v1_relat_1 @ X16))),
% 1.30/1.49      inference('cnf', [status(esa)], [t87_relat_1])).
% 1.30/1.49  thf(d10_xboole_0, axiom,
% 1.30/1.49    (![A:$i,B:$i]:
% 1.30/1.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.30/1.49  thf('34', plain,
% 1.30/1.49      (![X0 : $i, X2 : $i]:
% 1.30/1.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.30/1.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.30/1.49  thf('35', plain,
% 1.30/1.49      (![X0 : $i, X1 : $i]:
% 1.30/1.49         (~ (v1_relat_1 @ X1)
% 1.30/1.49          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.30/1.49          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.49  thf('36', plain,
% 1.30/1.49      (((((sk_C) = (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)))
% 1.30/1.49         | ~ (v1_relat_1 @ sk_A)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['32', '35'])).
% 1.30/1.49  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('38', plain,
% 1.30/1.49      ((((sk_C) = (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['36', '37'])).
% 1.30/1.49  thf('39', plain,
% 1.30/1.49      (((((sk_C) != (sk_C))
% 1.30/1.49         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 1.30/1.49            (k1_relat_1 @ sk_B))
% 1.30/1.49         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 1.30/1.49         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['23', '38'])).
% 1.30/1.49  thf('40', plain,
% 1.30/1.49      (((~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 1.30/1.49         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))
% 1.30/1.49         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 1.30/1.49            (k1_relat_1 @ sk_B))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('simplify', [status(thm)], ['39'])).
% 1.30/1.49  thf('41', plain,
% 1.30/1.49      (((~ (v1_relat_1 @ sk_A)
% 1.30/1.49         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 1.30/1.49            (k1_relat_1 @ sk_B))
% 1.30/1.49         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['4', '40'])).
% 1.30/1.49  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('43', plain,
% 1.30/1.49      ((((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 1.30/1.49          (k1_relat_1 @ sk_B))
% 1.30/1.49         | ~ (v1_funct_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['41', '42'])).
% 1.30/1.49  thf('44', plain,
% 1.30/1.49      (((~ (v1_relat_1 @ sk_A)
% 1.30/1.49         | ~ (v1_funct_1 @ sk_A)
% 1.30/1.49         | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 1.30/1.49            (k1_relat_1 @ sk_B))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['3', '43'])).
% 1.30/1.49  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('46', plain, ((v1_funct_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('47', plain,
% 1.30/1.49      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_C)) @ 
% 1.30/1.49         (k1_relat_1 @ sk_B)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.30/1.49  thf('48', plain,
% 1.30/1.49      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 1.30/1.49         | ~ (v1_relat_1 @ sk_A)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup+', [status(thm)], ['2', '47'])).
% 1.30/1.49  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('50', plain,
% 1.30/1.49      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['48', '49'])).
% 1.30/1.49  thf('51', plain,
% 1.30/1.49      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 1.30/1.49        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 1.30/1.49        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('52', plain,
% 1.30/1.49      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 1.30/1.49         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 1.30/1.49      inference('split', [status(esa)], ['51'])).
% 1.30/1.49  thf('53', plain,
% 1.30/1.49      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.30/1.49       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 1.30/1.49      inference('sup-', [status(thm)], ['50', '52'])).
% 1.30/1.49  thf('54', plain,
% 1.30/1.49      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 1.30/1.49       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.30/1.49       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 1.30/1.49      inference('split', [status(esa)], ['51'])).
% 1.30/1.49  thf('55', plain,
% 1.30/1.49      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 1.30/1.49         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 1.30/1.49      inference('split', [status(esa)], ['0'])).
% 1.30/1.49  thf('56', plain,
% 1.30/1.49      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 1.30/1.49      inference('split', [status(esa)], ['7'])).
% 1.30/1.49  thf(t163_funct_1, axiom,
% 1.30/1.49    (![A:$i,B:$i,C:$i]:
% 1.30/1.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.30/1.49       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 1.30/1.49           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 1.30/1.49         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.30/1.49  thf('57', plain,
% 1.30/1.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.30/1.49         (~ (r1_tarski @ X25 @ (k1_relat_1 @ X26))
% 1.30/1.49          | ~ (r1_tarski @ (k9_relat_1 @ X26 @ X25) @ X27)
% 1.30/1.49          | (r1_tarski @ X25 @ (k10_relat_1 @ X26 @ X27))
% 1.30/1.49          | ~ (v1_funct_1 @ X26)
% 1.30/1.49          | ~ (v1_relat_1 @ X26))),
% 1.30/1.49      inference('cnf', [status(esa)], [t163_funct_1])).
% 1.30/1.49  thf('58', plain,
% 1.30/1.49      ((![X0 : $i]:
% 1.30/1.49          (~ (v1_relat_1 @ sk_A)
% 1.30/1.49           | ~ (v1_funct_1 @ sk_A)
% 1.30/1.49           | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 1.30/1.49           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['56', '57'])).
% 1.30/1.49  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('60', plain, ((v1_funct_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('61', plain,
% 1.30/1.49      ((![X0 : $i]:
% 1.30/1.49          ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 1.30/1.49           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 1.30/1.49      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.30/1.49  thf('62', plain,
% 1.30/1.49      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) & 
% 1.30/1.49             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['55', '61'])).
% 1.30/1.49  thf(t182_relat_1, axiom,
% 1.30/1.49    (![A:$i]:
% 1.30/1.49     ( ( v1_relat_1 @ A ) =>
% 1.30/1.49       ( ![B:$i]:
% 1.30/1.49         ( ( v1_relat_1 @ B ) =>
% 1.30/1.49           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.30/1.49             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.30/1.49  thf('63', plain,
% 1.30/1.49      (![X12 : $i, X13 : $i]:
% 1.30/1.49         (~ (v1_relat_1 @ X12)
% 1.30/1.49          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 1.30/1.49              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 1.30/1.49          | ~ (v1_relat_1 @ X13))),
% 1.30/1.49      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.30/1.49  thf('64', plain,
% 1.30/1.49      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 1.30/1.49         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('split', [status(esa)], ['51'])).
% 1.30/1.49  thf('65', plain,
% 1.30/1.49      (((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.30/1.49         | ~ (v1_relat_1 @ sk_A)
% 1.30/1.49         | ~ (v1_relat_1 @ sk_B)))
% 1.30/1.49         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup-', [status(thm)], ['63', '64'])).
% 1.30/1.49  thf('66', plain, ((v1_relat_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('68', plain,
% 1.30/1.49      ((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 1.30/1.49         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.30/1.49  thf('69', plain,
% 1.30/1.49      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.30/1.49       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 1.30/1.49       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 1.30/1.49      inference('sup-', [status(thm)], ['62', '68'])).
% 1.30/1.49  thf('70', plain,
% 1.30/1.49      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.30/1.49       ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))),
% 1.30/1.49      inference('split', [status(esa)], ['7'])).
% 1.30/1.49  thf('71', plain,
% 1.30/1.49      ((((sk_C) = (k1_relat_1 @ (k7_relat_1 @ sk_A @ sk_C))))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['36', '37'])).
% 1.30/1.49  thf(t89_relat_1, axiom,
% 1.30/1.49    (![A:$i,B:$i]:
% 1.30/1.49     ( ( v1_relat_1 @ B ) =>
% 1.30/1.49       ( r1_tarski @
% 1.30/1.49         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 1.30/1.49  thf('72', plain,
% 1.30/1.49      (![X18 : $i, X19 : $i]:
% 1.30/1.49         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X18 @ X19)) @ 
% 1.30/1.49           (k1_relat_1 @ X18))
% 1.30/1.49          | ~ (v1_relat_1 @ X18))),
% 1.30/1.49      inference('cnf', [status(esa)], [t89_relat_1])).
% 1.30/1.49  thf('73', plain,
% 1.30/1.49      ((((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('sup+', [status(thm)], ['71', '72'])).
% 1.30/1.49  thf('74', plain, ((v1_relat_1 @ sk_A)),
% 1.30/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.49  thf('75', plain,
% 1.30/1.49      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 1.30/1.49         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.30/1.49      inference('demod', [status(thm)], ['73', '74'])).
% 1.30/1.49  thf('76', plain,
% 1.30/1.49      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 1.30/1.49         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 1.30/1.49      inference('split', [status(esa)], ['51'])).
% 1.30/1.49  thf('77', plain,
% 1.30/1.49      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.30/1.49       ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))),
% 1.30/1.49      inference('sup-', [status(thm)], ['75', '76'])).
% 1.30/1.49  thf('78', plain, ($false),
% 1.30/1.49      inference('sat_resolution*', [status(thm)],
% 1.30/1.49                ['1', '53', '54', '69', '70', '77'])).
% 1.30/1.49  
% 1.30/1.49  % SZS output end Refutation
% 1.30/1.49  
% 1.30/1.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
