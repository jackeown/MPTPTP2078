%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L8mmpBGTSz

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:20 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 148 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  901 (2127 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( r1_tarski @ ( k9_relat_1 @ X6 @ X4 ) @ ( k9_relat_1 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
        | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ X0 @ sk_C_1 ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_C_1 ) @ X1 )
        | ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_C_1 ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X15 @ ( k10_relat_1 @ X15 @ X16 ) ) @ X16 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,
    ( ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
      | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('30',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
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

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X18 @ X17 ) @ X19 )
      | ( r1_tarski @ X17 @ ( k10_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      & ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('40',plain,
    ( ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_B )
        | ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k10_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
        | ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

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

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k10_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('57',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k10_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) )
        | ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
      | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ sk_C_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','28','29','44','45','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L8mmpBGTSz
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.37/1.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.37/1.57  % Solved by: fo/fo7.sh
% 1.37/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.57  % done 1049 iterations in 1.115s
% 1.37/1.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.37/1.57  % SZS output start Refutation
% 1.37/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.37/1.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.37/1.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.37/1.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.37/1.57  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.37/1.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.37/1.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.37/1.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.37/1.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.37/1.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.37/1.57  thf(t171_funct_1, conjecture,
% 1.37/1.57    (![A:$i]:
% 1.37/1.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.37/1.57       ( ![B:$i]:
% 1.37/1.57         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.37/1.57           ( ![C:$i]:
% 1.37/1.57             ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 1.37/1.57               ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 1.37/1.57                 ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ))).
% 1.37/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.57    (~( ![A:$i]:
% 1.37/1.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.37/1.57          ( ![B:$i]:
% 1.37/1.57            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.37/1.57              ( ![C:$i]:
% 1.37/1.57                ( ( r1_tarski @ C @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) <=>
% 1.37/1.57                  ( ( r1_tarski @ C @ ( k1_relat_1 @ A ) ) & 
% 1.37/1.57                    ( r1_tarski @ ( k9_relat_1 @ A @ C ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) ) )),
% 1.37/1.57    inference('cnf.neg', [status(esa)], [t171_funct_1])).
% 1.37/1.57  thf('0', plain,
% 1.37/1.57      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 1.37/1.57        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('1', plain,
% 1.37/1.57      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.37/1.57       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 1.37/1.57      inference('split', [status(esa)], ['0'])).
% 1.37/1.57  thf(d3_tarski, axiom,
% 1.37/1.57    (![A:$i,B:$i]:
% 1.37/1.57     ( ( r1_tarski @ A @ B ) <=>
% 1.37/1.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.37/1.57  thf('2', plain,
% 1.37/1.57      (![X1 : $i, X3 : $i]:
% 1.37/1.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.37/1.57      inference('cnf', [status(esa)], [d3_tarski])).
% 1.37/1.57  thf(t182_relat_1, axiom,
% 1.37/1.57    (![A:$i]:
% 1.37/1.57     ( ( v1_relat_1 @ A ) =>
% 1.37/1.57       ( ![B:$i]:
% 1.37/1.57         ( ( v1_relat_1 @ B ) =>
% 1.37/1.57           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.37/1.57             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.37/1.57  thf('3', plain,
% 1.37/1.57      (![X7 : $i, X8 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X7)
% 1.37/1.57          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.37/1.57              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.37/1.57          | ~ (v1_relat_1 @ X8))),
% 1.37/1.57      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.37/1.57  thf('4', plain,
% 1.37/1.57      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 1.37/1.57        | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('5', plain,
% 1.37/1.57      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('split', [status(esa)], ['4'])).
% 1.37/1.57  thf('6', plain,
% 1.37/1.57      ((((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.37/1.57         | ~ (v1_relat_1 @ sk_A)
% 1.37/1.57         | ~ (v1_relat_1 @ sk_B)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup+', [status(thm)], ['3', '5'])).
% 1.37/1.57  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('9', plain,
% 1.37/1.57      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.37/1.57  thf(t156_relat_1, axiom,
% 1.37/1.57    (![A:$i,B:$i,C:$i]:
% 1.37/1.57     ( ( v1_relat_1 @ C ) =>
% 1.37/1.57       ( ( r1_tarski @ A @ B ) =>
% 1.37/1.57         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 1.37/1.57  thf('10', plain,
% 1.37/1.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.37/1.57         (~ (r1_tarski @ X4 @ X5)
% 1.37/1.57          | ~ (v1_relat_1 @ X6)
% 1.37/1.57          | (r1_tarski @ (k9_relat_1 @ X6 @ X4) @ (k9_relat_1 @ X6 @ X5)))),
% 1.37/1.57      inference('cnf', [status(esa)], [t156_relat_1])).
% 1.37/1.57  thf('11', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_C_1) @ 
% 1.37/1.57            (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 1.37/1.57           | ~ (v1_relat_1 @ X0)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['9', '10'])).
% 1.37/1.57  thf('12', plain,
% 1.37/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.57         (~ (r2_hidden @ X0 @ X1)
% 1.37/1.57          | (r2_hidden @ X0 @ X2)
% 1.37/1.57          | ~ (r1_tarski @ X1 @ X2))),
% 1.37/1.57      inference('cnf', [status(esa)], [d3_tarski])).
% 1.37/1.57  thf('13', plain,
% 1.37/1.57      ((![X0 : $i, X1 : $i]:
% 1.37/1.57          (~ (v1_relat_1 @ X0)
% 1.37/1.57           | (r2_hidden @ X1 @ 
% 1.37/1.57              (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 1.37/1.57           | ~ (r2_hidden @ X1 @ (k9_relat_1 @ X0 @ sk_C_1))))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['11', '12'])).
% 1.37/1.57  thf('14', plain,
% 1.37/1.57      ((![X0 : $i, X1 : $i]:
% 1.37/1.57          ((r1_tarski @ (k9_relat_1 @ X0 @ sk_C_1) @ X1)
% 1.37/1.57           | (r2_hidden @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_C_1)) @ 
% 1.37/1.57              (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 1.37/1.57           | ~ (v1_relat_1 @ X0)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['2', '13'])).
% 1.37/1.57  thf(t145_funct_1, axiom,
% 1.37/1.57    (![A:$i,B:$i]:
% 1.37/1.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.37/1.57       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 1.37/1.57  thf('15', plain,
% 1.37/1.57      (![X15 : $i, X16 : $i]:
% 1.37/1.57         ((r1_tarski @ (k9_relat_1 @ X15 @ (k10_relat_1 @ X15 @ X16)) @ X16)
% 1.37/1.57          | ~ (v1_funct_1 @ X15)
% 1.37/1.57          | ~ (v1_relat_1 @ X15))),
% 1.37/1.57      inference('cnf', [status(esa)], [t145_funct_1])).
% 1.37/1.57  thf('16', plain,
% 1.37/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.57         (~ (r2_hidden @ X0 @ X1)
% 1.37/1.57          | (r2_hidden @ X0 @ X2)
% 1.37/1.57          | ~ (r1_tarski @ X1 @ X2))),
% 1.37/1.57      inference('cnf', [status(esa)], [d3_tarski])).
% 1.37/1.57  thf('17', plain,
% 1.37/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X1)
% 1.37/1.57          | ~ (v1_funct_1 @ X1)
% 1.37/1.57          | (r2_hidden @ X2 @ X0)
% 1.37/1.57          | ~ (r2_hidden @ X2 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['15', '16'])).
% 1.37/1.57  thf('18', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          (~ (v1_relat_1 @ sk_A)
% 1.37/1.57           | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)
% 1.37/1.57           | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_A @ sk_C_1)) @ 
% 1.37/1.57              (k1_relat_1 @ sk_B))
% 1.37/1.57           | ~ (v1_funct_1 @ sk_A)
% 1.37/1.57           | ~ (v1_relat_1 @ sk_A)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['14', '17'])).
% 1.37/1.57  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('20', plain, ((v1_funct_1 @ sk_A)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('22', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)
% 1.37/1.57           | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_A @ sk_C_1)) @ 
% 1.37/1.57              (k1_relat_1 @ sk_B))))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 1.37/1.57  thf('23', plain,
% 1.37/1.57      (![X1 : $i, X3 : $i]:
% 1.37/1.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.37/1.57      inference('cnf', [status(esa)], [d3_tarski])).
% 1.37/1.57  thf('24', plain,
% 1.37/1.57      ((((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 1.37/1.57         | (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['22', '23'])).
% 1.37/1.57  thf('25', plain,
% 1.37/1.57      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('simplify', [status(thm)], ['24'])).
% 1.37/1.57  thf('26', plain,
% 1.37/1.57      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))
% 1.37/1.57        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 1.37/1.57        | ~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('27', plain,
% 1.37/1.57      ((~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 1.37/1.57         <= (~
% 1.37/1.57             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 1.37/1.57      inference('split', [status(esa)], ['26'])).
% 1.37/1.57  thf('28', plain,
% 1.37/1.57      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.37/1.57       ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 1.37/1.57      inference('sup-', [status(thm)], ['25', '27'])).
% 1.37/1.57  thf('29', plain,
% 1.37/1.57      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 1.37/1.57       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.37/1.57       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 1.37/1.57      inference('split', [status(esa)], ['26'])).
% 1.37/1.57  thf('30', plain,
% 1.37/1.57      (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))
% 1.37/1.57         <= (((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 1.37/1.57      inference('split', [status(esa)], ['0'])).
% 1.37/1.57  thf('31', plain,
% 1.37/1.57      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 1.37/1.57      inference('split', [status(esa)], ['4'])).
% 1.37/1.57  thf(t163_funct_1, axiom,
% 1.37/1.57    (![A:$i,B:$i,C:$i]:
% 1.37/1.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.37/1.57       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 1.37/1.57           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 1.37/1.57         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.37/1.57  thf('32', plain,
% 1.37/1.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.37/1.57         (~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 1.37/1.57          | ~ (r1_tarski @ (k9_relat_1 @ X18 @ X17) @ X19)
% 1.37/1.57          | (r1_tarski @ X17 @ (k10_relat_1 @ X18 @ X19))
% 1.37/1.57          | ~ (v1_funct_1 @ X18)
% 1.37/1.57          | ~ (v1_relat_1 @ X18))),
% 1.37/1.57      inference('cnf', [status(esa)], [t163_funct_1])).
% 1.37/1.57  thf('33', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          (~ (v1_relat_1 @ sk_A)
% 1.37/1.57           | ~ (v1_funct_1 @ sk_A)
% 1.37/1.57           | (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 1.37/1.57           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['31', '32'])).
% 1.37/1.57  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('35', plain, ((v1_funct_1 @ sk_A)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('36', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          ((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ X0))
% 1.37/1.57           | ~ (r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ X0)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 1.37/1.57      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.37/1.57  thf('37', plain,
% 1.37/1.57      (((r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) & 
% 1.37/1.57             ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['30', '36'])).
% 1.37/1.57  thf('38', plain,
% 1.37/1.57      (![X7 : $i, X8 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X7)
% 1.37/1.57          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.37/1.57              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.37/1.57          | ~ (v1_relat_1 @ X8))),
% 1.37/1.57      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.37/1.57  thf('39', plain,
% 1.37/1.57      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 1.37/1.57         <= (~
% 1.37/1.57             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('split', [status(esa)], ['26'])).
% 1.37/1.57  thf('40', plain,
% 1.37/1.57      (((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.37/1.57         | ~ (v1_relat_1 @ sk_A)
% 1.37/1.57         | ~ (v1_relat_1 @ sk_B)))
% 1.37/1.57         <= (~
% 1.37/1.57             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['38', '39'])).
% 1.37/1.57  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('43', plain,
% 1.37/1.57      ((~ (r1_tarski @ sk_C_1 @ (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 1.37/1.57         <= (~
% 1.37/1.57             ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.37/1.57  thf('44', plain,
% 1.37/1.57      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.37/1.57       ~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))) | 
% 1.37/1.57       ~ ((r1_tarski @ (k9_relat_1 @ sk_A @ sk_C_1) @ (k1_relat_1 @ sk_B)))),
% 1.37/1.57      inference('sup-', [status(thm)], ['37', '43'])).
% 1.37/1.57  thf('45', plain,
% 1.37/1.57      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.37/1.57       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 1.37/1.57      inference('split', [status(esa)], ['4'])).
% 1.37/1.57  thf('46', plain,
% 1.37/1.57      (![X7 : $i, X8 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X7)
% 1.37/1.57          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.37/1.57              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.37/1.57          | ~ (v1_relat_1 @ X8))),
% 1.37/1.57      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.37/1.57  thf('47', plain,
% 1.37/1.57      (![X1 : $i, X3 : $i]:
% 1.37/1.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.37/1.57      inference('cnf', [status(esa)], [d3_tarski])).
% 1.37/1.57  thf('48', plain,
% 1.37/1.57      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B))))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('split', [status(esa)], ['4'])).
% 1.37/1.57  thf('49', plain,
% 1.37/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.37/1.57         (~ (r2_hidden @ X0 @ X1)
% 1.37/1.57          | (r2_hidden @ X0 @ X2)
% 1.37/1.57          | ~ (r1_tarski @ X1 @ X2))),
% 1.37/1.57      inference('cnf', [status(esa)], [d3_tarski])).
% 1.37/1.57  thf('50', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          ((r2_hidden @ X0 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))
% 1.37/1.57           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['48', '49'])).
% 1.37/1.57  thf('51', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          ((r1_tarski @ sk_C_1 @ X0)
% 1.37/1.57           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 1.37/1.57              (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['47', '50'])).
% 1.37/1.57  thf('52', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 1.37/1.57            (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.37/1.57           | ~ (v1_relat_1 @ sk_A)
% 1.37/1.57           | ~ (v1_relat_1 @ sk_B)
% 1.37/1.57           | (r1_tarski @ sk_C_1 @ X0)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup+', [status(thm)], ['46', '51'])).
% 1.37/1.57  thf('53', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('55', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 1.37/1.57            (k10_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 1.37/1.57           | (r1_tarski @ sk_C_1 @ X0)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('demod', [status(thm)], ['52', '53', '54'])).
% 1.37/1.57  thf(d13_funct_1, axiom,
% 1.37/1.57    (![A:$i]:
% 1.37/1.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.37/1.57       ( ![B:$i,C:$i]:
% 1.37/1.57         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 1.37/1.57           ( ![D:$i]:
% 1.37/1.57             ( ( r2_hidden @ D @ C ) <=>
% 1.37/1.57               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 1.37/1.57                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 1.37/1.57  thf('56', plain,
% 1.37/1.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.37/1.57         (((X12) != (k10_relat_1 @ X11 @ X10))
% 1.37/1.57          | (r2_hidden @ X13 @ (k1_relat_1 @ X11))
% 1.37/1.57          | ~ (r2_hidden @ X13 @ X12)
% 1.37/1.57          | ~ (v1_funct_1 @ X11)
% 1.37/1.57          | ~ (v1_relat_1 @ X11))),
% 1.37/1.57      inference('cnf', [status(esa)], [d13_funct_1])).
% 1.37/1.57  thf('57', plain,
% 1.37/1.57      (![X10 : $i, X11 : $i, X13 : $i]:
% 1.37/1.57         (~ (v1_relat_1 @ X11)
% 1.37/1.57          | ~ (v1_funct_1 @ X11)
% 1.37/1.57          | ~ (r2_hidden @ X13 @ (k10_relat_1 @ X11 @ X10))
% 1.37/1.57          | (r2_hidden @ X13 @ (k1_relat_1 @ X11)))),
% 1.37/1.57      inference('simplify', [status(thm)], ['56'])).
% 1.37/1.57  thf('58', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          ((r1_tarski @ sk_C_1 @ X0)
% 1.37/1.57           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))
% 1.37/1.57           | ~ (v1_funct_1 @ sk_A)
% 1.37/1.57           | ~ (v1_relat_1 @ sk_A)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['55', '57'])).
% 1.37/1.57  thf('59', plain, ((v1_funct_1 @ sk_A)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 1.37/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.57  thf('61', plain,
% 1.37/1.57      ((![X0 : $i]:
% 1.37/1.57          ((r1_tarski @ sk_C_1 @ X0)
% 1.37/1.57           | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_A))))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.37/1.57  thf('62', plain,
% 1.37/1.57      (![X1 : $i, X3 : $i]:
% 1.37/1.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.37/1.57      inference('cnf', [status(esa)], [d3_tarski])).
% 1.37/1.57  thf('63', plain,
% 1.37/1.57      ((((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))
% 1.37/1.57         | (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('sup-', [status(thm)], ['61', '62'])).
% 1.37/1.57  thf('64', plain,
% 1.37/1.57      (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 1.37/1.57         <= (((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))))),
% 1.37/1.57      inference('simplify', [status(thm)], ['63'])).
% 1.37/1.57  thf('65', plain,
% 1.37/1.57      ((~ (r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))
% 1.37/1.57         <= (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A))))),
% 1.37/1.57      inference('split', [status(esa)], ['26'])).
% 1.37/1.57  thf('66', plain,
% 1.37/1.57      (~ ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ (k5_relat_1 @ sk_A @ sk_B)))) | 
% 1.37/1.57       ((r1_tarski @ sk_C_1 @ (k1_relat_1 @ sk_A)))),
% 1.37/1.57      inference('sup-', [status(thm)], ['64', '65'])).
% 1.37/1.57  thf('67', plain, ($false),
% 1.37/1.57      inference('sat_resolution*', [status(thm)],
% 1.37/1.57                ['1', '28', '29', '44', '45', '66'])).
% 1.37/1.57  
% 1.37/1.57  % SZS output end Refutation
% 1.37/1.57  
% 1.37/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
