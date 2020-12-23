%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0xKhEtLxhu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 124 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  706 (1785 expanded)
%              Number of equality atoms :    8 (  10 expanded)
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

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('3',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('16',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
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

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X15 @ X14 ) @ X16 )
      | ( r1_tarski @ X14 @ ( k10_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('27',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('35',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k9_relat_1 @ X7 @ X5 ) @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( ( k2_xboole_0 @ ( k9_relat_1 @ X0 @ sk_C ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
          = ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C ) @ X1 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','14','15','31','32','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0xKhEtLxhu
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:05:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 192 iterations in 0.100s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.54  thf(t171_funct_1, conjecture,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.19/0.54               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.54                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i]:
% 0.19/0.54        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.54          ( ![B:$i]:
% 0.19/0.54            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.54              ( ![C:$i]:
% 0.19/0.54                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.19/0.54                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.54                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.19/0.54        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.19/0.54       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf(t44_relat_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( v1_relat_1 @ B ) =>
% 0.19/0.54           ( r1_tarski @
% 0.19/0.54             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.19/0.54  thf('2', plain,
% 0.19/0.54      (![X10 : $i, X11 : $i]:
% 0.19/0.54         (~ (v1_relat_1 @ X10)
% 0.19/0.54          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 0.19/0.54             (k1_relat_1 @ X11))
% 0.19/0.54          | ~ (v1_relat_1 @ X11))),
% 0.19/0.54      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.19/0.54  thf('3', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf(t12_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.54  thf('4', plain,
% 0.19/0.54      (![X3 : $i, X4 : $i]:
% 0.19/0.54         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.19/0.54      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      ((((k2_xboole_0 @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 0.19/0.54          = (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.54  thf(t11_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.19/0.54  thf('7', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          (~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)
% 0.19/0.54           | (r1_tarski @ sk_C @ X0)))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      (((~ (v1_relat_1 @ sk_A)
% 0.19/0.54         | ~ (v1_relat_1 @ sk_B)
% 0.19/0.54         | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['2', '7'])).
% 0.19/0.54  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('11', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.19/0.54  thf('12', plain,
% 0.19/0.54      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.19/0.54        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.19/0.54        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('13', plain,
% 0.19/0.54      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.19/0.54         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.19/0.54      inference('split', [status(esa)], ['12'])).
% 0.19/0.54  thf('14', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.19/0.54       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['11', '13'])).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.19/0.54       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.19/0.54       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.19/0.54      inference('split', [status(esa)], ['12'])).
% 0.19/0.54  thf('16', plain,
% 0.19/0.54      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.19/0.54        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('17', plain,
% 0.19/0.54      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.19/0.54         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.19/0.54      inference('split', [status(esa)], ['16'])).
% 0.19/0.54  thf('18', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf(t163_funct_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.54       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.19/0.54           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.19/0.54         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.54         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.19/0.54          | ~ (r1_tarski @ (k9_relat_1 @ X15 @ X14) @ X16)
% 0.19/0.54          | (r1_tarski @ X14 @ (k10_relat_1 @ X15 @ X16))
% 0.19/0.54          | ~ (v1_funct_1 @ X15)
% 0.19/0.54          | ~ (v1_relat_1 @ X15))),
% 0.19/0.54      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.19/0.54  thf('20', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          (~ (v1_relat_1 @ sk_A)
% 0.19/0.54           | ~ (v1_funct_1 @ sk_A)
% 0.19/0.54           | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.19/0.54           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.54  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('22', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('23', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.19/0.54           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.19/0.54      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) & 
% 0.19/0.54             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['17', '23'])).
% 0.19/0.54  thf(t182_relat_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( v1_relat_1 @ B ) =>
% 0.19/0.54           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.54             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.19/0.54  thf('25', plain,
% 0.19/0.54      (![X8 : $i, X9 : $i]:
% 0.19/0.54         (~ (v1_relat_1 @ X8)
% 0.19/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.19/0.54              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.19/0.54          | ~ (v1_relat_1 @ X9))),
% 0.19/0.54      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.19/0.54  thf('26', plain,
% 0.19/0.54      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.19/0.54         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('split', [status(esa)], ['12'])).
% 0.19/0.54  thf('27', plain,
% 0.19/0.54      (((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.54         | ~ (v1_relat_1 @ sk_A)
% 0.19/0.54         | ~ (v1_relat_1 @ sk_B)))
% 0.19/0.54         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.54  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('30', plain,
% 0.19/0.54      ((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.19/0.54         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.19/0.54  thf('31', plain,
% 0.19/0.54      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.19/0.54       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.19/0.54       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['24', '30'])).
% 0.19/0.54  thf('32', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.19/0.54       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.19/0.54      inference('split', [status(esa)], ['16'])).
% 0.19/0.54  thf(t145_funct_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.54       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.19/0.54  thf('33', plain,
% 0.19/0.54      (![X12 : $i, X13 : $i]:
% 0.19/0.54         ((r1_tarski @ (k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X13)) @ X13)
% 0.19/0.54          | ~ (v1_funct_1 @ X12)
% 0.19/0.54          | ~ (v1_relat_1 @ X12))),
% 0.19/0.54      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.19/0.54  thf('34', plain,
% 0.19/0.54      (![X8 : $i, X9 : $i]:
% 0.19/0.54         (~ (v1_relat_1 @ X8)
% 0.19/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.19/0.54              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.19/0.54          | ~ (v1_relat_1 @ X9))),
% 0.19/0.54      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.19/0.54  thf('35', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('36', plain,
% 0.19/0.54      ((((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.54         | ~ (v1_relat_1 @ sk_A)
% 0.19/0.54         | ~ (v1_relat_1 @ sk_B)))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('sup+', [status(thm)], ['34', '35'])).
% 0.19/0.54  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('39', plain,
% 0.19/0.54      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.19/0.54  thf(t156_relat_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ C ) =>
% 0.19/0.54       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.54         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.54  thf('40', plain,
% 0.19/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.54         (~ (r1_tarski @ X5 @ X6)
% 0.19/0.54          | ~ (v1_relat_1 @ X7)
% 0.19/0.54          | (r1_tarski @ (k9_relat_1 @ X7 @ X5) @ (k9_relat_1 @ X7 @ X6)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.19/0.54  thf('41', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_C) @ 
% 0.19/0.54            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.19/0.54           | ~ (v1_relat_1 @ X0)))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.54  thf('42', plain,
% 0.19/0.54      (![X3 : $i, X4 : $i]:
% 0.19/0.54         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.19/0.54      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.54  thf('43', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          (~ (v1_relat_1 @ X0)
% 0.19/0.54           | ((k2_xboole_0 @ (k9_relat_1 @ X0 @ sk_C) @ 
% 0.19/0.54               (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.19/0.54               = (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.54  thf('44', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.19/0.54  thf('45', plain,
% 0.19/0.54      ((![X0 : $i, X1 : $i]:
% 0.19/0.54          (~ (r1_tarski @ 
% 0.19/0.54              (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.19/0.54              X1)
% 0.19/0.54           | ~ (v1_relat_1 @ X0)
% 0.19/0.54           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_C) @ X1)))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.54  thf('46', plain,
% 0.19/0.54      (((~ (v1_relat_1 @ sk_A)
% 0.19/0.54         | ~ (v1_funct_1 @ sk_A)
% 0.19/0.54         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.19/0.54         | ~ (v1_relat_1 @ sk_A)))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['33', '45'])).
% 0.19/0.54  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('48', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('50', plain,
% 0.19/0.54      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.19/0.54         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.19/0.54      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.19/0.54  thf('51', plain,
% 0.19/0.54      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.19/0.54         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.19/0.54      inference('split', [status(esa)], ['12'])).
% 0.19/0.54  thf('52', plain,
% 0.19/0.54      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.19/0.54       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.54  thf('53', plain, ($false),
% 0.19/0.54      inference('sat_resolution*', [status(thm)],
% 0.19/0.54                ['1', '14', '15', '31', '32', '52'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
