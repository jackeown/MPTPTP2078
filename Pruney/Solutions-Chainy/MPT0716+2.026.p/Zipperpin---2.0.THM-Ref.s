%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2yF19S62xL

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  702 (1835 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X6 @ X7 ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        | ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 )
        | ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('18',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
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

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X13 @ X12 ) @ X14 )
      | ( r1_tarski @ X12 @ ( k10_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['14'])).

thf('29',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('37',plain,
    ( ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k9_relat_1 @ X5 @ X3 ) @ ( k9_relat_1 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C ) @ X1 )
        | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) @ X1 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X0 )
        | ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_C ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_C ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','45'])).

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
    inference(split,[status(esa)],['14'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','16','17','33','34','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2yF19S62xL
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 96 iterations in 0.079s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(t171_funct_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.20/0.53               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.53                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.20/0.53                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.53                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.20/0.53        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.20/0.53       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf(t167_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         ((r1_tarski @ (k10_relat_1 @ X6 @ X7) @ (k1_relat_1 @ X6))
% 0.20/0.53          | ~ (v1_relat_1 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.20/0.53  thf(t182_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( v1_relat_1 @ B ) =>
% 0.20/0.53           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.53             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X8)
% 0.20/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.20/0.53              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.20/0.53          | ~ (v1_relat_1 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf(t1_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.53       ( r1_tarski @ A @ C ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.53          | (r1_tarski @ X0 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((r1_tarski @ sk_C @ X0)
% 0.20/0.53           | ~ (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)) @ X0)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 0.20/0.53           | ~ (v1_relat_1 @ sk_A)
% 0.20/0.53           | ~ (v1_relat_1 @ sk_B)
% 0.20/0.53           | (r1_tarski @ sk_C @ X0)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.53  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)
% 0.20/0.53           | (r1_tarski @ sk_C @ X0)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_A) | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '10'])).
% 0.20/0.53  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.20/0.53        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))
% 0.20/0.53        | ~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.20/0.53       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.20/0.53       ~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.20/0.53       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['14'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))
% 0.20/0.53        | (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.20/0.53         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf(t163_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.53       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.53           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.20/0.53         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 0.20/0.53          | ~ (r1_tarski @ (k9_relat_1 @ X13 @ X12) @ X14)
% 0.20/0.53          | (r1_tarski @ X12 @ (k10_relat_1 @ X13 @ X14))
% 0.20/0.53          | ~ (v1_funct_1 @ X13)
% 0.20/0.53          | ~ (v1_relat_1 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (v1_relat_1 @ sk_A)
% 0.20/0.53           | ~ (v1_funct_1 @ sk_A)
% 0.20/0.53           | (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.20/0.53           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ X0))
% 0.20/0.53           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ X0)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) & 
% 0.20/0.53             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X8)
% 0.20/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.20/0.53              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.20/0.53          | ~ (v1_relat_1 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('split', [status(esa)], ['14'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.20/0.53         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.53         | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_A))) | 
% 0.20/0.53       ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.20/0.53       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.20/0.53       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf(t145_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         ((r1_tarski @ (k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X11)) @ X11)
% 0.20/0.53          | ~ (v1_funct_1 @ X10)
% 0.20/0.53          | ~ (v1_relat_1 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X8)
% 0.20/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.20/0.53              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.20/0.53          | ~ (v1_relat_1 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf(t156_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.53         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X3 @ X4)
% 0.20/0.53          | ~ (v1_relat_1 @ X5)
% 0.20/0.53          | (r1_tarski @ (k9_relat_1 @ X5 @ X3) @ (k9_relat_1 @ X5 @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_C) @ 
% 0.20/0.53            (k9_relat_1 @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.20/0.53           | ~ (v1_relat_1 @ X0)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.53          | (r1_tarski @ X0 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      ((![X0 : $i, X1 : $i]:
% 0.20/0.53          (~ (v1_relat_1 @ X0)
% 0.20/0.53           | (r1_tarski @ (k9_relat_1 @ X0 @ sk_C) @ X1)
% 0.20/0.53           | ~ (r1_tarski @ 
% 0.20/0.53                (k9_relat_1 @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))) @ 
% 0.20/0.53                X1)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((![X0 : $i, X1 : $i]:
% 0.20/0.53          (~ (r1_tarski @ 
% 0.20/0.53              (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.20/0.53              X0)
% 0.20/0.53           | ~ (v1_relat_1 @ sk_A)
% 0.20/0.53           | ~ (v1_relat_1 @ sk_B)
% 0.20/0.53           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_C) @ X0)
% 0.20/0.53           | ~ (v1_relat_1 @ X1)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '41'])).
% 0.20/0.53  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((![X0 : $i, X1 : $i]:
% 0.20/0.53          (~ (r1_tarski @ 
% 0.20/0.53              (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.20/0.53              X0)
% 0.20/0.53           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_C) @ X0)
% 0.20/0.53           | ~ (v1_relat_1 @ X1)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_A)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_A)
% 0.20/0.53         | ~ (v1_relat_1 @ sk_A)
% 0.20/0.53         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '45'])).
% 0.20/0.53  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('48', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('49', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.20/0.53         <= (((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))
% 0.20/0.53         <= (~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['14'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (~ ((r1_tarski @ sk_C @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.20/0.53       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.53  thf('53', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)],
% 0.20/0.53                ['1', '16', '17', '33', '34', '52'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
