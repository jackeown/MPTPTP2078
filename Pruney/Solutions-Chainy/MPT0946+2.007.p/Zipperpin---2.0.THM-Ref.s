%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c3XTmFKbli

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:28 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  212 (2794 expanded)
%              Number of leaves         :   27 ( 825 expanded)
%              Depth                    :   53
%              Number of atoms          : 1735 (28794 expanded)
%              Number of equality atoms :   91 (1855 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r2_hidden @ X5 @ X4 )
      | ( X5 = X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('1',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r2_hidden @ X5 @ X4 )
      | ( X5 = X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X3 )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_ordinal1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t19_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ ( k2_wellord1 @ X13 @ X14 ) ) )
      | ( r2_hidden @ X12 @ ( k3_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
       != ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ X20 )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('12',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X19 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
        = X19 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('13',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('14',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('16',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( r1_ordinal1 @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r2_hidden @ X5 @ X4 )
      | ( X5 = X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k1_wellord1 @ X8 @ X7 ) )
      | ( X10 != X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_wellord1 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( X0 = X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X0 @ X2 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X2 )
      | ~ ( v3_ordinal1 @ X2 )
      | ( X0 = X2 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ( r2_hidden @ X5 @ X4 )
      | ( X5 = X4 )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('35',plain,(
    ! [X26: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X26 ) )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t11_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord2])).

thf('36',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_wellord1 @ X17 )
      | ~ ( r4_wellord1 @ X17 @ ( k2_wellord1 @ X17 @ ( k1_wellord1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k3_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('42',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','54'])).

thf('56',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('63',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_wellord1 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('72',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ( r1_ordinal1 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X3 )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_ordinal1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ X0 )
        = ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ ( k2_wellord1 @ X13 @ X14 ) ) )
      | ( r2_hidden @ X12 @ ( k3_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('85',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('86',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['71','87'])).

thf('89',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r2_hidden @ sk_A @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['70','91'])).

thf('93',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X3 )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_ordinal1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('94',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('99',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('101',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('103',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r4_wellord1 @ X15 @ X16 )
      | ~ ( r4_wellord1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('106',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('107',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['101','107','108','109'])).

thf('111',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','112'])).

thf('114',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','115'])).

thf('117',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( sk_B = sk_A )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('123',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( sk_B
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B ) )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_wellord1 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('128',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('130',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_B )
    | ( r1_ordinal1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['119','120'])).

thf('132',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    = ( k1_wellord2 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('133',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ ( k2_wellord1 @ X13 @ X14 ) ) )
      | ( r2_hidden @ X12 @ ( k3_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('136',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('137',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['131','138'])).

thf('140',plain,(
    r1_ordinal1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['130','139'])).

thf('141',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ~ ( v3_ordinal1 @ X3 )
      | ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_ordinal1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('142',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X28 ) @ X27 )
        = ( k1_wellord2 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('147',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
    = ( k1_wellord2 @ sk_B ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('149',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','155'])).

thf('157',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','158'])).

thf('160',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( X25
        = ( k1_wellord1 @ ( k1_wellord2 @ X24 ) @ X25 ) )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('167',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ X7 @ ( k1_wellord1 @ X8 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('172',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_A )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['163','164'])).

thf('174',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
    = ( k1_wellord2 @ sk_B ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('175',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_relat_1 @ ( k2_wellord1 @ X13 @ X14 ) ) )
      | ( r2_hidden @ X12 @ ( k3_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('178',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('179',plain,(
    ! [X19: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['176','177','178','179'])).

thf('181',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['173','180'])).

thf('182',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('183',plain,(
    $false ),
    inference(demod,[status(thm)],['172','181','182'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c3XTmFKbli
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 123 iterations in 0.126s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.61  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.39/0.61  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.39/0.61  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.61  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.39/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.61  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.39/0.61  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.39/0.61  thf(t24_ordinal1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.39/0.61                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.39/0.61  thf('0', plain,
% 0.39/0.61      (![X4 : $i, X5 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X4)
% 0.39/0.61          | (r2_hidden @ X5 @ X4)
% 0.39/0.61          | ((X5) = (X4))
% 0.39/0.61          | (r2_hidden @ X4 @ X5)
% 0.39/0.61          | ~ (v3_ordinal1 @ X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.39/0.61  thf(t7_wellord2, axiom,
% 0.39/0.61    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (![X26 : $i]:
% 0.39/0.61         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      (![X4 : $i, X5 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X4)
% 0.39/0.61          | (r2_hidden @ X5 @ X4)
% 0.39/0.61          | ((X5) = (X4))
% 0.39/0.61          | (r2_hidden @ X4 @ X5)
% 0.39/0.61          | ~ (v3_ordinal1 @ X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.39/0.61  thf(connectedness_r1_ordinal1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.39/0.61       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ X1 @ X0))),
% 0.39/0.61      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.39/0.61  thf(redefinition_r1_ordinal1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.39/0.61       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (![X2 : $i, X3 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X2)
% 0.39/0.61          | ~ (v3_ordinal1 @ X3)
% 0.39/0.61          | (r1_tarski @ X2 @ X3)
% 0.39/0.61          | ~ (r1_ordinal1 @ X2 @ X3))),
% 0.39/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_tarski @ X1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_tarski @ X1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1))),
% 0.39/0.61      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.61  thf(t8_wellord2, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r1_tarski @ A @ B ) =>
% 0.39/0.61       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      (![X27 : $i, X28 : $i]:
% 0.39/0.61         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.39/0.61          | ~ (r1_tarski @ X27 @ X28))),
% 0.39/0.61      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.61  thf(t19_wellord1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ C ) =>
% 0.39/0.61       ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) ) =>
% 0.39/0.61         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) ) ))).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X12 @ (k3_relat_1 @ (k2_wellord1 @ X13 @ X14)))
% 0.39/0.61          | (r2_hidden @ X12 @ (k3_relat_1 @ X13))
% 0.39/0.61          | ~ (v1_relat_1 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X2 @ (k3_relat_1 @ (k1_wellord2 @ X0)))
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ X1 @ X0)
% 0.39/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.39/0.61          | (r2_hidden @ X2 @ (k3_relat_1 @ (k1_wellord2 @ X1))))),
% 0.39/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.61  thf(d1_wellord2, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ B ) =>
% 0.39/0.61       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.39/0.61         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.39/0.61           ( ![C:$i,D:$i]:
% 0.39/0.61             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.39/0.61               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.39/0.61                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      (![X19 : $i, X20 : $i]:
% 0.39/0.61         (((X20) != (k1_wellord2 @ X19))
% 0.39/0.61          | ((k3_relat_1 @ X20) = (X19))
% 0.39/0.61          | ~ (v1_relat_1 @ X20))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X19 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ (k1_wellord2 @ X19))
% 0.39/0.61          | ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.61  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.39/0.61  thf('13', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.61  thf('14', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.39/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.61  thf('15', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.61  thf('16', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.39/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X2 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ X1 @ X0)
% 0.39/0.61          | (r2_hidden @ X2 @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['10', '14', '15', '16'])).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r2_hidden @ X0 @ X1)
% 0.39/0.61          | ((X1) = (X0))
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r2_hidden @ X1 @ X2)
% 0.39/0.61          | (r1_ordinal1 @ X2 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X2)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['2', '17'])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X2)
% 0.39/0.61          | (r1_ordinal1 @ X2 @ X0)
% 0.39/0.61          | (r2_hidden @ X1 @ X2)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ((X1) = (X0))
% 0.39/0.61          | (r2_hidden @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.39/0.61      inference('simplify', [status(thm)], ['18'])).
% 0.39/0.61  thf('20', plain,
% 0.39/0.61      (![X4 : $i, X5 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X4)
% 0.39/0.61          | (r2_hidden @ X5 @ X4)
% 0.39/0.61          | ((X5) = (X4))
% 0.39/0.61          | (r2_hidden @ X4 @ X5)
% 0.39/0.61          | ~ (v3_ordinal1 @ X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.39/0.61  thf(t10_wellord2, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61           ( ( r2_hidden @ A @ B ) =>
% 0.39/0.61             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (![X24 : $i, X25 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X24)
% 0.39/0.61          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.39/0.61          | ~ (r2_hidden @ X25 @ X24)
% 0.39/0.61          | ~ (v3_ordinal1 @ X25))),
% 0.39/0.61      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r2_hidden @ X0 @ X1)
% 0.39/0.61          | ((X1) = (X0))
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.39/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ((X1) = (X0))
% 0.39/0.61          | (r2_hidden @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.39/0.61      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.61  thf(d1_wellord1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ A ) =>
% 0.39/0.61       ( ![B:$i,C:$i]:
% 0.39/0.61         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.39/0.61           ( ![D:$i]:
% 0.39/0.61             ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.61               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.61         (((X9) != (k1_wellord1 @ X8 @ X7))
% 0.39/0.61          | ((X10) != (X7))
% 0.39/0.61          | ~ (r2_hidden @ X10 @ X9)
% 0.39/0.61          | ~ (v1_relat_1 @ X8))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X7 : $i, X8 : $i]:
% 0.39/0.61         (~ (v1_relat_1 @ X8) | ~ (r2_hidden @ X7 @ (k1_wellord1 @ X8 @ X7)))),
% 0.39/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X0 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r2_hidden @ X1 @ X0)
% 0.39/0.61          | ((X0) = (X1))
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | ~ (v1_relat_1 @ (k1_wellord2 @ X1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['23', '25'])).
% 0.39/0.61  thf('27', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X0 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r2_hidden @ X1 @ X0)
% 0.39/0.61          | ((X0) = (X1))
% 0.39/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.39/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.61  thf('29', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r2_hidden @ X2 @ X0)
% 0.39/0.61          | ((X0) = (X2))
% 0.39/0.61          | ~ (v3_ordinal1 @ X2)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X2)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | ((X0) = (X1))
% 0.39/0.61          | (r2_hidden @ X1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['19', '28'])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((r2_hidden @ X1 @ X0)
% 0.39/0.61          | ((X0) = (X1))
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X2)
% 0.39/0.61          | ~ (v3_ordinal1 @ X2)
% 0.39/0.61          | ((X0) = (X2))
% 0.39/0.61          | (r2_hidden @ X2 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r2_hidden @ X1 @ X0)
% 0.39/0.61          | ((X0) = (X1))
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | ((X0) = (X1)))),
% 0.39/0.61      inference('eq_fact', [status(thm)], ['30'])).
% 0.39/0.61  thf('32', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | ((X0) = (X1))
% 0.39/0.61          | (r2_hidden @ X1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (![X26 : $i]:
% 0.39/0.61         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (![X4 : $i, X5 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X4)
% 0.39/0.61          | (r2_hidden @ X5 @ X4)
% 0.39/0.61          | ((X5) = (X4))
% 0.39/0.61          | (r2_hidden @ X4 @ X5)
% 0.39/0.61          | ~ (v3_ordinal1 @ X5))),
% 0.39/0.61      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.39/0.61  thf('35', plain,
% 0.39/0.61      (![X26 : $i]:
% 0.39/0.61         ((v2_wellord1 @ (k1_wellord2 @ X26)) | ~ (v3_ordinal1 @ X26))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.39/0.61  thf(t11_wellord2, conjecture,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.39/0.61             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i]:
% 0.39/0.61        ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61          ( ![B:$i]:
% 0.39/0.61            ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.39/0.61                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.39/0.61  thf('36', plain,
% 0.39/0.61      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('37', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ((X1) = (X0))
% 0.39/0.61          | (r2_hidden @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1))),
% 0.39/0.61      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.61  thf(t57_wellord1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v1_relat_1 @ A ) =>
% 0.39/0.61       ( ( v2_wellord1 @ A ) =>
% 0.39/0.61         ( ![B:$i]:
% 0.39/0.61           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.39/0.61                ( r4_wellord1 @
% 0.39/0.61                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.39/0.61  thf('39', plain,
% 0.39/0.61      (![X17 : $i, X18 : $i]:
% 0.39/0.61         (~ (v2_wellord1 @ X17)
% 0.39/0.61          | ~ (r4_wellord1 @ X17 @ 
% 0.39/0.61               (k2_wellord1 @ X17 @ (k1_wellord1 @ X17 @ X18)))
% 0.39/0.62          | ~ (r2_hidden @ X18 @ (k3_relat_1 @ X17))
% 0.39/0.62          | ~ (v1_relat_1 @ X17))),
% 0.39/0.62      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.39/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.39/0.62          | ~ (v3_ordinal1 @ X0)
% 0.39/0.62          | (r2_hidden @ X1 @ X0)
% 0.39/0.62          | ((X0) = (X1))
% 0.39/0.62          | ~ (v3_ordinal1 @ X1)
% 0.39/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.39/0.62          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.39/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.62  thf('41', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.62  thf('42', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.39/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.39/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.39/0.62          | ~ (v3_ordinal1 @ X0)
% 0.39/0.62          | (r2_hidden @ X1 @ X0)
% 0.39/0.62          | ((X0) = (X1))
% 0.39/0.62          | ~ (v3_ordinal1 @ X1)
% 0.39/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.39/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.39/0.62          | ~ (v3_ordinal1 @ X0)
% 0.39/0.62          | ~ (v3_ordinal1 @ X1)
% 0.39/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.39/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.39/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.39/0.62          | ~ (v3_ordinal1 @ X1)
% 0.39/0.62          | ((X0) = (X1))
% 0.39/0.62          | (r2_hidden @ X1 @ X0)
% 0.39/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['37', '43'])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((r2_hidden @ X1 @ X0)
% 0.39/0.62          | ((X0) = (X1))
% 0.39/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.39/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.39/0.62          | (r1_ordinal1 @ X1 @ X0)
% 0.39/0.62          | ~ (v3_ordinal1 @ X1)
% 0.39/0.62          | ~ (v3_ordinal1 @ X0)
% 0.39/0.62          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['44'])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      ((~ (v3_ordinal1 @ sk_B)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.62        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.62        | ((sk_B) = (sk_A))
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['36', '45'])).
% 0.39/0.62  thf('47', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('48', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.62        | ((sk_B) = (sk_A))
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.39/0.62  thf('50', plain, (((sk_A) != (sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      ((~ (v3_ordinal1 @ sk_A)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.62        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['35', '51'])).
% 0.39/0.62  thf('53', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      (((r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.62        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['52', '53'])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      ((~ (v3_ordinal1 @ sk_B)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | ((sk_B) = (sk_A))
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.62        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['34', '54'])).
% 0.39/0.62  thf('56', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('57', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('58', plain,
% 0.39/0.62      (((r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | ((sk_B) = (sk_A))
% 0.39/0.62        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | ((sk_B) = (sk_A))
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('simplify', [status(thm)], ['58'])).
% 0.39/0.62  thf('60', plain, (((sk_A) != (sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('61', plain, (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (![X24 : $i, X25 : $i]:
% 0.39/0.62         (~ (v3_ordinal1 @ X24)
% 0.39/0.62          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.39/0.62          | ~ (r2_hidden @ X25 @ X24)
% 0.39/0.62          | ~ (v3_ordinal1 @ X25))),
% 0.39/0.62      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.62        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.39/0.62  thf('64', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('65', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('66', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.39/0.62  thf('67', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X8) | ~ (r2_hidden @ X7 @ (k1_wellord1 @ X8 @ X7)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.62  thf('68', plain,
% 0.39/0.62      ((~ (r2_hidden @ sk_A @ sk_A)
% 0.39/0.62        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.39/0.62  thf('69', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      ((~ (r2_hidden @ sk_A @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('71', plain, (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.39/0.62  thf('72', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (v3_ordinal1 @ X0)
% 0.39/0.62          | ~ (v3_ordinal1 @ X1)
% 0.39/0.62          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.62          | (r1_ordinal1 @ X1 @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.39/0.62  thf('74', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((r1_ordinal1 @ X0 @ sk_A)
% 0.39/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.39/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.39/0.62  thf('75', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i]:
% 0.39/0.62         (~ (v3_ordinal1 @ X2)
% 0.39/0.62          | ~ (v3_ordinal1 @ X3)
% 0.39/0.62          | (r1_tarski @ X2 @ X3)
% 0.39/0.62          | ~ (r1_ordinal1 @ X2 @ X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v3_ordinal1 @ X0)
% 0.39/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.39/0.62          | (r1_tarski @ X0 @ sk_A)
% 0.39/0.62          | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.39/0.62  thf('77', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('78', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v3_ordinal1 @ X0)
% 0.39/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.39/0.62          | (r1_tarski @ X0 @ sk_A)
% 0.39/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['76', '77'])).
% 0.39/0.62  thf('79', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((r1_tarski @ X0 @ sk_A)
% 0.39/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.39/0.62          | ~ (v3_ordinal1 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['78'])).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      (![X27 : $i, X28 : $i]:
% 0.39/0.62         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.39/0.62          | ~ (r1_tarski @ X27 @ X28))),
% 0.39/0.62      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.39/0.62  thf('81', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v3_ordinal1 @ X0)
% 0.39/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.39/0.62          | ((k2_wellord1 @ (k1_wellord2 @ sk_A) @ X0) = (k1_wellord2 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['79', '80'])).
% 0.39/0.62  thf('82', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X12 @ (k3_relat_1 @ (k2_wellord1 @ X13 @ X14)))
% 0.39/0.62          | (r2_hidden @ X12 @ (k3_relat_1 @ X13))
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.39/0.62  thf('83', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X1 @ (k3_relat_1 @ (k1_wellord2 @ X0)))
% 0.39/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.39/0.62          | ~ (v3_ordinal1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.39/0.62          | (r2_hidden @ X1 @ (k3_relat_1 @ (k1_wellord2 @ sk_A))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['81', '82'])).
% 0.39/0.62  thf('84', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.39/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('85', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.62  thf('86', plain, (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.39/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('87', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X1 @ X0)
% 0.39/0.62          | (r1_ordinal1 @ sk_A @ X0)
% 0.39/0.62          | ~ (v3_ordinal1 @ X0)
% 0.39/0.62          | (r2_hidden @ X1 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 0.39/0.62  thf('88', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_A)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_B)
% 0.39/0.62        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['71', '87'])).
% 0.39/0.62  thf('89', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('90', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_A @ sk_B)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_A)
% 0.39/0.62        | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['88', '89'])).
% 0.39/0.62  thf('91', plain, (((r2_hidden @ sk_A @ sk_A) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.39/0.62      inference('simplify', [status(thm)], ['90'])).
% 0.39/0.62  thf('92', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.39/0.62      inference('clc', [status(thm)], ['70', '91'])).
% 0.39/0.62  thf('93', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i]:
% 0.39/0.62         (~ (v3_ordinal1 @ X2)
% 0.39/0.62          | ~ (v3_ordinal1 @ X3)
% 0.39/0.62          | (r1_tarski @ X2 @ X3)
% 0.39/0.62          | ~ (r1_ordinal1 @ X2 @ X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.62  thf('94', plain,
% 0.39/0.62      (((r1_tarski @ sk_A @ sk_B)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_B)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['92', '93'])).
% 0.39/0.62  thf('95', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('96', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('97', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.62      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.39/0.62  thf('98', plain,
% 0.39/0.62      (![X27 : $i, X28 : $i]:
% 0.39/0.62         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.39/0.62          | ~ (r1_tarski @ X27 @ X28))),
% 0.39/0.62      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.39/0.62  thf('99', plain,
% 0.39/0.62      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['97', '98'])).
% 0.39/0.62  thf('100', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.39/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.39/0.62          | ~ (v3_ordinal1 @ X0)
% 0.39/0.62          | (r2_hidden @ X1 @ X0)
% 0.39/0.62          | ((X0) = (X1))
% 0.39/0.62          | ~ (v3_ordinal1 @ X1)
% 0.39/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.39/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.39/0.62  thf('101', plain,
% 0.39/0.62      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.39/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.39/0.62        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_B)
% 0.39/0.62        | ((sk_A) = (sk_B))
% 0.39/0.62        | (r2_hidden @ sk_B @ sk_A)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['99', '100'])).
% 0.39/0.62  thf('102', plain,
% 0.39/0.62      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t50_wellord1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( v1_relat_1 @ A ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( v1_relat_1 @ B ) =>
% 0.39/0.62           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.39/0.62  thf('103', plain,
% 0.39/0.62      (![X15 : $i, X16 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X15)
% 0.39/0.62          | (r4_wellord1 @ X15 @ X16)
% 0.39/0.62          | ~ (r4_wellord1 @ X16 @ X15)
% 0.39/0.62          | ~ (v1_relat_1 @ X16))),
% 0.39/0.62      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.39/0.62  thf('104', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.39/0.62        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.39/0.62        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['102', '103'])).
% 0.39/0.62  thf('105', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.62  thf('106', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.62  thf('107', plain,
% 0.39/0.62      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.39/0.62  thf('108', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('109', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('110', plain,
% 0.39/0.62      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.39/0.62        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | ((sk_A) = (sk_B))
% 0.39/0.62        | (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['101', '107', '108', '109'])).
% 0.39/0.62  thf('111', plain, (((sk_A) != (sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('112', plain,
% 0.39/0.62      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.39/0.62        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 0.39/0.62  thf('113', plain,
% 0.39/0.62      ((~ (v3_ordinal1 @ sk_B)
% 0.39/0.62        | (r2_hidden @ sk_B @ sk_A)
% 0.39/0.62        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['33', '112'])).
% 0.39/0.62  thf('114', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('115', plain,
% 0.39/0.62      (((r2_hidden @ sk_B @ sk_A) | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['113', '114'])).
% 0.39/0.62  thf('116', plain,
% 0.39/0.62      ((~ (v3_ordinal1 @ sk_B)
% 0.39/0.62        | ((sk_B) = (sk_A))
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.62        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.39/0.62        | (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['32', '115'])).
% 0.39/0.62  thf('117', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('118', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('119', plain,
% 0.39/0.62      ((((sk_B) = (sk_A))
% 0.39/0.62        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.39/0.62        | (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.39/0.62  thf('120', plain, (((sk_A) != (sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('121', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_B @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['119', '120'])).
% 0.39/0.62  thf('122', plain,
% 0.39/0.62      (![X24 : $i, X25 : $i]:
% 0.39/0.62         (~ (v3_ordinal1 @ X24)
% 0.39/0.62          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.39/0.62          | ~ (r2_hidden @ X25 @ X24)
% 0.39/0.62          | ~ (v3_ordinal1 @ X25))),
% 0.39/0.62      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.39/0.62  thf('123', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_B @ sk_A)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_B)
% 0.39/0.62        | ((sk_B) = (k1_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B))
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['121', '122'])).
% 0.39/0.62  thf('124', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('125', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('126', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_B @ sk_A)
% 0.39/0.62        | ((sk_B) = (k1_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.39/0.62  thf('127', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X8) | ~ (r2_hidden @ X7 @ (k1_wellord1 @ X8 @ X7)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.62  thf('128', plain,
% 0.39/0.62      ((~ (r2_hidden @ sk_B @ sk_B)
% 0.39/0.62        | (r1_ordinal1 @ sk_B @ sk_A)
% 0.39/0.62        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['126', '127'])).
% 0.39/0.62  thf('129', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.62  thf('130', plain,
% 0.39/0.62      ((~ (r2_hidden @ sk_B @ sk_B) | (r1_ordinal1 @ sk_B @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['128', '129'])).
% 0.39/0.62  thf('131', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_B @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['119', '120'])).
% 0.39/0.62  thf('132', plain,
% 0.39/0.62      (((k2_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (k1_wellord2 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['97', '98'])).
% 0.39/0.62  thf('133', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X12 @ (k3_relat_1 @ (k2_wellord1 @ X13 @ X14)))
% 0.39/0.62          | (r2_hidden @ X12 @ (k3_relat_1 @ X13))
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.39/0.62  thf('134', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ sk_A)))
% 0.39/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.39/0.62          | (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ sk_B))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['132', '133'])).
% 0.39/0.62  thf('135', plain,
% 0.39/0.62      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.39/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('136', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.62  thf('137', plain,
% 0.39/0.62      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.39/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('138', plain,
% 0.39/0.62      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 0.39/0.62  thf('139', plain,
% 0.39/0.62      (((r1_ordinal1 @ sk_B @ sk_A) | (r2_hidden @ sk_B @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['131', '138'])).
% 0.39/0.62  thf('140', plain, ((r1_ordinal1 @ sk_B @ sk_A)),
% 0.39/0.62      inference('clc', [status(thm)], ['130', '139'])).
% 0.39/0.62  thf('141', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i]:
% 0.39/0.62         (~ (v3_ordinal1 @ X2)
% 0.39/0.62          | ~ (v3_ordinal1 @ X3)
% 0.39/0.62          | (r1_tarski @ X2 @ X3)
% 0.39/0.62          | ~ (r1_ordinal1 @ X2 @ X3))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.62  thf('142', plain,
% 0.39/0.62      (((r1_tarski @ sk_B @ sk_A)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['140', '141'])).
% 0.39/0.62  thf('143', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('144', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('145', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.39/0.62  thf('146', plain,
% 0.39/0.62      (![X27 : $i, X28 : $i]:
% 0.39/0.62         (((k2_wellord1 @ (k1_wellord2 @ X28) @ X27) = (k1_wellord2 @ X27))
% 0.39/0.62          | ~ (r1_tarski @ X27 @ X28))),
% 0.39/0.62      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.39/0.62  thf('147', plain,
% 0.39/0.62      (((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['145', '146'])).
% 0.39/0.62  thf('148', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.39/0.62             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.39/0.62          | ~ (v3_ordinal1 @ X0)
% 0.39/0.62          | (r2_hidden @ X1 @ X0)
% 0.39/0.62          | ((X0) = (X1))
% 0.39/0.62          | ~ (v3_ordinal1 @ X1)
% 0.39/0.62          | ~ (r2_hidden @ X0 @ X1)
% 0.39/0.62          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.39/0.62  thf('149', plain,
% 0.39/0.62      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))
% 0.39/0.62        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.62        | ((sk_B) = (sk_A))
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['147', '148'])).
% 0.39/0.62  thf('150', plain,
% 0.39/0.62      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('151', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('152', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('153', plain,
% 0.39/0.62      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.62        | ((sk_B) = (sk_A))
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 0.39/0.62  thf('154', plain, (((sk_A) != (sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('155', plain,
% 0.39/0.62      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.39/0.62        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['153', '154'])).
% 0.39/0.62  thf('156', plain,
% 0.39/0.62      ((~ (v3_ordinal1 @ sk_A)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '155'])).
% 0.39/0.62  thf('157', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('158', plain,
% 0.39/0.62      (((r2_hidden @ sk_A @ sk_B) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['156', '157'])).
% 0.39/0.62  thf('159', plain,
% 0.39/0.62      ((~ (v3_ordinal1 @ sk_B)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | ((sk_B) = (sk_A))
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['0', '158'])).
% 0.39/0.62  thf('160', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('161', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('162', plain,
% 0.39/0.62      (((r2_hidden @ sk_A @ sk_B)
% 0.39/0.62        | ((sk_B) = (sk_A))
% 0.39/0.62        | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.39/0.62  thf('163', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.62      inference('simplify', [status(thm)], ['162'])).
% 0.39/0.62  thf('164', plain, (((sk_A) != (sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('165', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['163', '164'])).
% 0.39/0.62  thf('166', plain,
% 0.39/0.62      (![X24 : $i, X25 : $i]:
% 0.39/0.62         (~ (v3_ordinal1 @ X24)
% 0.39/0.62          | ((X25) = (k1_wellord1 @ (k1_wellord2 @ X24) @ X25))
% 0.39/0.62          | ~ (r2_hidden @ X25 @ X24)
% 0.39/0.62          | ~ (v3_ordinal1 @ X25))),
% 0.39/0.62      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.39/0.62  thf('167', plain,
% 0.39/0.62      ((~ (v3_ordinal1 @ sk_A)
% 0.39/0.62        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.39/0.62        | ~ (v3_ordinal1 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['165', '166'])).
% 0.39/0.62  thf('168', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('169', plain, ((v3_ordinal1 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('170', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['167', '168', '169'])).
% 0.39/0.62  thf('171', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X8) | ~ (r2_hidden @ X7 @ (k1_wellord1 @ X8 @ X7)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.62  thf('172', plain,
% 0.39/0.62      ((~ (r2_hidden @ sk_A @ sk_A) | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['170', '171'])).
% 0.39/0.62  thf('173', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['163', '164'])).
% 0.39/0.62  thf('174', plain,
% 0.39/0.62      (((k2_wellord1 @ (k1_wellord2 @ sk_A) @ sk_B) = (k1_wellord2 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['145', '146'])).
% 0.39/0.62  thf('175', plain,
% 0.39/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X12 @ (k3_relat_1 @ (k2_wellord1 @ X13 @ X14)))
% 0.39/0.62          | (r2_hidden @ X12 @ (k3_relat_1 @ X13))
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t19_wellord1])).
% 0.39/0.62  thf('176', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ sk_B)))
% 0.39/0.62          | ~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.39/0.62          | (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ sk_A))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['174', '175'])).
% 0.39/0.62  thf('177', plain,
% 0.39/0.62      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.39/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('178', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.62  thf('179', plain,
% 0.39/0.62      (![X19 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X19)) = (X19))),
% 0.39/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf('180', plain,
% 0.39/0.62      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['176', '177', '178', '179'])).
% 0.39/0.62  thf('181', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.39/0.62      inference('sup-', [status(thm)], ['173', '180'])).
% 0.39/0.62  thf('182', plain, (![X23 : $i]: (v1_relat_1 @ (k1_wellord2 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.39/0.62  thf('183', plain, ($false),
% 0.39/0.62      inference('demod', [status(thm)], ['172', '181', '182'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
