%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JKS3mKCELw

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:19 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 168 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  861 (2217 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X20 @ ( k10_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('4',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k9_relat_1 @ X11 @ X9 ) @ ( k9_relat_1 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) @ X0 )
        | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_C_1 ) @ X0 )
        | ~ ( v1_relat_1 @ X1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['30'])).

thf('34',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X23 @ X22 ) @ X24 )
      | ( r1_tarski @ X22 @ ( k10_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['30'])).

thf('44',plain,
    ( ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('50',plain,
    ( ( ( k2_xboole_0 @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      = ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X17
       != ( k10_relat_1 @ X16 @ X15 ) )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X16 ) )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k10_relat_1 @ X16 @ X15 ) )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','33','48','49','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JKS3mKCELw
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 502 iterations in 0.306s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.76  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.54/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.54/0.76  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.54/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.76  thf(t171_funct_1, conjecture,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.76           ( ![C:$i]:
% 0.54/0.76             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.54/0.76               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.54/0.76                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i]:
% 0.54/0.76        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.76          ( ![B:$i]:
% 0.54/0.76            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.76              ( ![C:$i]:
% 0.54/0.76                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 0.54/0.76                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 0.54/0.76                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 0.54/0.76  thf('0', plain,
% 0.54/0.76      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.54/0.76        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('1', plain,
% 0.54/0.76      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.54/0.76       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.54/0.76      inference('split', [status(esa)], ['0'])).
% 0.54/0.76  thf(t145_funct_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.76       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.54/0.76  thf('2', plain,
% 0.54/0.76      (![X20 : $i, X21 : $i]:
% 0.54/0.76         ((r1_tarski @ (k9_relat_1 @ X20 @ (k10_relat_1 @ X20 @ X21)) @ X21)
% 0.54/0.76          | ~ (v1_funct_1 @ X20)
% 0.54/0.76          | ~ (v1_relat_1 @ X20))),
% 0.54/0.76      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.54/0.76  thf(t182_relat_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( v1_relat_1 @ B ) =>
% 0.54/0.76           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.54/0.76             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.54/0.76  thf('3', plain,
% 0.54/0.76      (![X12 : $i, X13 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X12)
% 0.54/0.76          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.54/0.76              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.54/0.76          | ~ (v1_relat_1 @ X13))),
% 0.54/0.76      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.54/0.76  thf('4', plain,
% 0.54/0.76      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.54/0.76        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('5', plain,
% 0.54/0.76      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('split', [status(esa)], ['4'])).
% 0.54/0.76  thf('6', plain,
% 0.54/0.76      ((((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.54/0.76         | ~ (v1_relat_1 @ sk_A)
% 0.54/0.76         | ~ (v1_relat_1 @ sk_B)))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('sup+', [status(thm)], ['3', '5'])).
% 0.54/0.76  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('9', plain,
% 0.54/0.76      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.54/0.76  thf(t12_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.54/0.76  thf('10', plain,
% 0.54/0.76      (![X7 : $i, X8 : $i]:
% 0.54/0.76         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.54/0.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      ((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.54/0.76          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.76  thf(d3_tarski, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.76  thf('12', plain,
% 0.54/0.76      (![X1 : $i, X3 : $i]:
% 0.54/0.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.76  thf('13', plain,
% 0.54/0.76      (![X1 : $i, X3 : $i]:
% 0.54/0.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.76  thf('14', plain,
% 0.54/0.76      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.76  thf('15', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.54/0.76      inference('simplify', [status(thm)], ['14'])).
% 0.54/0.76  thf(t11_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.54/0.76  thf('16', plain,
% 0.54/0.76      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.54/0.76         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.54/0.76  thf('17', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf(t156_relat_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ C ) =>
% 0.54/0.76       ( ( r1_tarski @ A @ B ) =>
% 0.54/0.76         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.54/0.76  thf('18', plain,
% 0.54/0.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.54/0.76         (~ (r1_tarski @ X9 @ X10)
% 0.54/0.76          | ~ (v1_relat_1 @ X11)
% 0.54/0.76          | (r1_tarski @ (k9_relat_1 @ X11 @ X9) @ (k9_relat_1 @ X11 @ X10)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.54/0.76  thf('19', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 0.54/0.76           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.54/0.76          | ~ (v1_relat_1 @ X2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.76  thf('20', plain,
% 0.54/0.76      (![X7 : $i, X8 : $i]:
% 0.54/0.76         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.54/0.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.76  thf('21', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X2)
% 0.54/0.76          | ((k2_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ 
% 0.54/0.76              (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.54/0.76              = (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.76  thf('22', plain,
% 0.54/0.76      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.54/0.76         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.54/0.76  thf('23', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.76         (~ (r1_tarski @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.54/0.76          | ~ (v1_relat_1 @ X2)
% 0.54/0.76          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ X3))),
% 0.54/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      ((![X0 : $i, X1 : $i]:
% 0.54/0.76          (~ (r1_tarski @ 
% 0.54/0.76              (k9_relat_1 @ X1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))) @ 
% 0.54/0.76              X0)
% 0.54/0.76           | (r1_tarski @ (k9_relat_1 @ X1 @ sk_C_1) @ X0)
% 0.54/0.76           | ~ (v1_relat_1 @ X1)))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['11', '23'])).
% 0.54/0.76  thf('25', plain,
% 0.54/0.76      (((~ (v1_relat_1 @ sk_A)
% 0.54/0.76         | ~ (v1_funct_1 @ sk_A)
% 0.54/0.76         | ~ (v1_relat_1 @ sk_A)
% 0.54/0.76         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['2', '24'])).
% 0.54/0.76  thf('26', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('27', plain, ((v1_funct_1 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('29', plain,
% 0.54/0.76      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.54/0.76  thf('30', plain,
% 0.54/0.76      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 0.54/0.76        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.54/0.76        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('31', plain,
% 0.54/0.76      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.54/0.76         <= (~
% 0.54/0.76             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.54/0.76      inference('split', [status(esa)], ['30'])).
% 0.54/0.76  thf('32', plain,
% 0.54/0.76      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.54/0.76       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['29', '31'])).
% 0.54/0.76  thf('33', plain,
% 0.54/0.76      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.54/0.76       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.54/0.76       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.54/0.76      inference('split', [status(esa)], ['30'])).
% 0.54/0.76  thf('34', plain,
% 0.54/0.76      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 0.54/0.76         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.54/0.76      inference('split', [status(esa)], ['0'])).
% 0.54/0.76  thf('35', plain,
% 0.54/0.76      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.54/0.76      inference('split', [status(esa)], ['4'])).
% 0.54/0.76  thf(t163_funct_1, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.54/0.76       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.54/0.76           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.54/0.76         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.54/0.76  thf('36', plain,
% 0.54/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.76         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 0.54/0.76          | ~ (r1_tarski @ (k9_relat_1 @ X23 @ X22) @ X24)
% 0.54/0.76          | (r1_tarski @ X22 @ (k10_relat_1 @ X23 @ X24))
% 0.54/0.76          | ~ (v1_funct_1 @ X23)
% 0.54/0.76          | ~ (v1_relat_1 @ X23))),
% 0.54/0.76      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.54/0.76  thf('37', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          (~ (v1_relat_1 @ sk_A)
% 0.54/0.76           | ~ (v1_funct_1 @ sk_A)
% 0.54/0.76           | (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.54/0.76           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['35', '36'])).
% 0.54/0.76  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('39', plain, ((v1_funct_1 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('40', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          ((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 0.54/0.76           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.54/0.76      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.54/0.76  thf('41', plain,
% 0.54/0.76      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) & 
% 0.54/0.76             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['34', '40'])).
% 0.54/0.76  thf('42', plain,
% 0.54/0.76      (![X12 : $i, X13 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X12)
% 0.54/0.76          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.54/0.76              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.54/0.76          | ~ (v1_relat_1 @ X13))),
% 0.54/0.76      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.54/0.76  thf('43', plain,
% 0.54/0.76      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 0.54/0.76         <= (~
% 0.54/0.76             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('split', [status(esa)], ['30'])).
% 0.54/0.76  thf('44', plain,
% 0.54/0.76      (((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.54/0.76         | ~ (v1_relat_1 @ sk_A)
% 0.54/0.76         | ~ (v1_relat_1 @ sk_B)))
% 0.54/0.76         <= (~
% 0.54/0.76             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.76  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('47', plain,
% 0.54/0.76      ((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.54/0.76         <= (~
% 0.54/0.76             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.54/0.76  thf('48', plain,
% 0.54/0.76      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.54/0.76       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 0.54/0.76       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['41', '47'])).
% 0.54/0.76  thf('49', plain,
% 0.54/0.76      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.54/0.76       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 0.54/0.76      inference('split', [status(esa)], ['4'])).
% 0.54/0.76  thf('50', plain,
% 0.54/0.76      ((((k2_xboole_0 @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.54/0.76          = (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.76  thf('51', plain,
% 0.54/0.76      (![X1 : $i, X3 : $i]:
% 0.54/0.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.76  thf('52', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf('53', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X0 @ X1)
% 0.54/0.76          | (r2_hidden @ X0 @ X2)
% 0.54/0.76          | ~ (r1_tarski @ X1 @ X2))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.76  thf('54', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['52', '53'])).
% 0.54/0.76  thf('55', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.76         ((r1_tarski @ X0 @ X1)
% 0.54/0.76          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['51', '54'])).
% 0.54/0.76  thf('56', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.54/0.76            (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.54/0.76           | (r1_tarski @ sk_C_1 @ X0)))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('sup+', [status(thm)], ['50', '55'])).
% 0.54/0.76  thf(d13_funct_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.76       ( ![B:$i,C:$i]:
% 0.54/0.76         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.54/0.76           ( ![D:$i]:
% 0.54/0.76             ( ( r2_hidden @ D @ C ) <=>
% 0.54/0.76               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.54/0.76                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.54/0.76  thf('57', plain,
% 0.54/0.76      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.54/0.76         (((X17) != (k10_relat_1 @ X16 @ X15))
% 0.54/0.76          | (r2_hidden @ X18 @ (k1_relat_1 @ X16))
% 0.54/0.76          | ~ (r2_hidden @ X18 @ X17)
% 0.54/0.76          | ~ (v1_funct_1 @ X16)
% 0.54/0.76          | ~ (v1_relat_1 @ X16))),
% 0.54/0.76      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.54/0.76  thf('58', plain,
% 0.54/0.76      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X16)
% 0.54/0.76          | ~ (v1_funct_1 @ X16)
% 0.54/0.76          | ~ (r2_hidden @ X18 @ (k10_relat_1 @ X16 @ X15))
% 0.54/0.76          | (r2_hidden @ X18 @ (k1_relat_1 @ X16)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['57'])).
% 0.54/0.76  thf('59', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          ((r1_tarski @ sk_C_1 @ X0)
% 0.54/0.76           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))
% 0.54/0.76           | ~ (v1_funct_1 @ sk_A)
% 0.54/0.76           | ~ (v1_relat_1 @ sk_A)))
% 0.54/0.76         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['56', '58'])).
% 0.54/0.77  thf('60', plain, ((v1_funct_1 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('61', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('62', plain,
% 0.54/0.77      ((![X0 : $i]:
% 0.54/0.77          ((r1_tarski @ sk_C_1 @ X0)
% 0.54/0.77           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))))
% 0.54/0.77         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.77      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.54/0.77  thf('63', plain,
% 0.54/0.77      (![X1 : $i, X3 : $i]:
% 0.54/0.77         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.54/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.77  thf('64', plain,
% 0.54/0.77      ((((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 0.54/0.77         | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))
% 0.54/0.77         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.77      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.77  thf('65', plain,
% 0.54/0.77      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.54/0.77         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 0.54/0.77      inference('simplify', [status(thm)], ['64'])).
% 0.54/0.77  thf('66', plain,
% 0.54/0.77      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 0.54/0.77         <= (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 0.54/0.77      inference('split', [status(esa)], ['30'])).
% 0.54/0.77  thf('67', plain,
% 0.54/0.77      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 0.54/0.77       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['65', '66'])).
% 0.54/0.77  thf('68', plain, ($false),
% 0.54/0.77      inference('sat_resolution*', [status(thm)],
% 0.54/0.77                ['1', '32', '33', '48', '49', '67'])).
% 0.54/0.77  
% 0.54/0.77  % SZS output end Refutation
% 0.54/0.77  
% 0.62/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
