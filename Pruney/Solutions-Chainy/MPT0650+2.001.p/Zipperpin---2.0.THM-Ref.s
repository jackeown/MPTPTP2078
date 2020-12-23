%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MxIhDq8547

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:18 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 405 expanded)
%              Number of leaves         :   30 ( 129 expanded)
%              Depth                    :   33
%              Number of atoms          : 1269 (5520 expanded)
%              Number of equality atoms :   64 ( 360 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t57_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( v2_funct_1 @ B )
            & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
         => ( ( A
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
            & ( A
              = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_funct_1])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X9 @ X7 ) @ X9 ) @ X7 )
      | ( X8
       != ( k2_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('9',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X9 @ X7 ) @ X9 ) @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['7','9'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('16',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X30 ) )
      | ( X31
        = ( k1_funct_1 @ ( k2_funct_1 @ X30 ) @ ( k1_funct_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_B ) @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['7','9'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X32 @ X34 ) @ X33 )
      | ( X34
        = ( k1_funct_1 @ X33 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','26','27'])).

thf('29',plain,
    ( ( ( sk_D_1 @ sk_A @ sk_B )
      = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','33'])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X24 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X24 @ X25 ) @ ( k1_relat_1 @ X26 ) )
      | ( r2_hidden @ X25 @ ( k1_relat_1 @ ( k5_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('40',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('41',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('42',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','53'])).

thf('55',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','59'])).

thf('61',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ X0 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v5_relat_1 @ sk_B @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_B @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf(t22_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X27 @ X28 ) @ X29 )
        = ( k1_funct_1 @ X28 @ ( k1_funct_1 @ X27 @ X29 ) ) )
      | ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t22_funct_1])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('95',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('96',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k4_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93','96'])).

thf('98',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ X20 )
        = ( k4_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('99',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
    | ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(split,[status(esa)],['99'])).

thf('101',plain,
    ( ( ( sk_A
       != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) )
   <= ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,
    ( ( sk_D_1 @ sk_A @ sk_B )
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','26','27'])).

thf('107',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['99'])).

thf('108',plain,
    ( ( sk_A
     != ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('110',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( sk_A
     != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) )
    | ( sk_A
     != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['99'])).

thf('113',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['111','112'])).

thf('114',plain,(
    sk_A
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_B ) @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['105','113'])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['97','114'])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['121','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MxIhDq8547
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 133 iterations in 0.077s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.34/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.34/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.34/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.34/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.34/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.53  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.53  thf(dt_k4_relat_1, axiom,
% 0.34/0.53    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.34/0.53  thf(d9_funct_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.53       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      (![X20 : $i]:
% 0.34/0.53         (~ (v2_funct_1 @ X20)
% 0.34/0.53          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 0.34/0.53          | ~ (v1_funct_1 @ X20)
% 0.34/0.53          | ~ (v1_relat_1 @ X20))),
% 0.34/0.53      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.34/0.53  thf(dt_k2_funct_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.53       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.34/0.53         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X21 : $i]:
% 0.34/0.53         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 0.34/0.53          | ~ (v1_funct_1 @ X21)
% 0.34/0.53          | ~ (v1_relat_1 @ X21))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0)
% 0.34/0.53          | ~ (v1_funct_1 @ X0)
% 0.34/0.53          | ~ (v2_funct_1 @ X0)
% 0.34/0.53          | ~ (v1_relat_1 @ X0)
% 0.34/0.53          | ~ (v1_funct_1 @ X0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v2_funct_1 @ X0)
% 0.34/0.53          | ~ (v1_funct_1 @ X0)
% 0.34/0.53          | ~ (v1_relat_1 @ X0)
% 0.34/0.53          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.34/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v2_funct_1 @ X0)
% 0.34/0.53          | ~ (v1_funct_1 @ X0)
% 0.34/0.53          | ~ (v1_relat_1 @ X0)
% 0.34/0.53          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 0.34/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.34/0.53  thf(t57_funct_1, conjecture,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.34/0.53       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.34/0.53         ( ( ( A ) =
% 0.34/0.53             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.34/0.53           ( ( A ) =
% 0.34/0.53             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i]:
% 0.34/0.53        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.34/0.53          ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.34/0.53            ( ( ( A ) =
% 0.34/0.53                ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.34/0.53              ( ( A ) =
% 0.34/0.53                ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t57_funct_1])).
% 0.34/0.53  thf('7', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(d5_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.34/0.53       ( ![C:$i]:
% 0.34/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.34/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X9 @ X8)
% 0.34/0.53          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X9 @ X7) @ X9) @ X7)
% 0.34/0.53          | ((X8) != (k2_relat_1 @ X7)))),
% 0.34/0.53      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (![X7 : $i, X9 : $i]:
% 0.34/0.53         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X9 @ X7) @ X9) @ X7)
% 0.34/0.53          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X7)))),
% 0.34/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '9'])).
% 0.34/0.53  thf(t20_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ C ) =>
% 0.34/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.34/0.53         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.34/0.53           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.34/0.53         (~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18)
% 0.34/0.53          | (r2_hidden @ X16 @ (k1_relat_1 @ X18))
% 0.34/0.53          | ~ (v1_relat_1 @ X18))),
% 0.34/0.53      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.34/0.53        | (r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.53  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.34/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (![X20 : $i]:
% 0.34/0.53         (~ (v2_funct_1 @ X20)
% 0.34/0.53          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 0.34/0.53          | ~ (v1_funct_1 @ X20)
% 0.34/0.53          | ~ (v1_relat_1 @ X20))),
% 0.34/0.53      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_B))),
% 0.34/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.34/0.53  thf(t56_funct_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.34/0.53       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.34/0.53         ( ( ( A ) =
% 0.34/0.53             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.34/0.53           ( ( A ) =
% 0.34/0.53             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (![X30 : $i, X31 : $i]:
% 0.34/0.53         (~ (v2_funct_1 @ X30)
% 0.34/0.53          | ~ (r2_hidden @ X31 @ (k1_relat_1 @ X30))
% 0.34/0.53          | ((X31)
% 0.34/0.53              = (k1_funct_1 @ (k2_funct_1 @ X30) @ (k1_funct_1 @ X30 @ X31)))
% 0.34/0.53          | ~ (v1_funct_1 @ X30)
% 0.34/0.53          | ~ (v1_relat_1 @ X30))),
% 0.34/0.53      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.34/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.34/0.53        | ((sk_D_1 @ sk_A @ sk_B)
% 0.34/0.53            = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ 
% 0.34/0.53               (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.34/0.53        | ~ (v2_funct_1 @ sk_B))),
% 0.34/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.53  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_B) @ sk_A) @ sk_B)),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '9'])).
% 0.34/0.53  thf(t8_funct_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.34/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.34/0.53         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.34/0.53           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.34/0.53         (~ (r2_hidden @ (k4_tarski @ X32 @ X34) @ X33)
% 0.34/0.53          | ((X34) = (k1_funct_1 @ X33 @ X32))
% 0.34/0.53          | ~ (v1_funct_1 @ X33)
% 0.34/0.53          | ~ (v1_relat_1 @ X33))),
% 0.34/0.53      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.34/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.34/0.53        | ((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.34/0.53  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('26', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.34/0.53      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.34/0.53  thf('27', plain, ((v2_funct_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('28', plain,
% 0.34/0.53      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['18', '19', '20', '26', '27'])).
% 0.34/0.53  thf('29', plain,
% 0.34/0.53      ((((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))
% 0.34/0.53        | ~ (v1_relat_1 @ sk_B)
% 0.34/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.34/0.53        | ~ (v2_funct_1 @ sk_B))),
% 0.34/0.53      inference('sup+', [status(thm)], ['15', '28'])).
% 0.34/0.53  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('32', plain, ((v2_funct_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      ((r2_hidden @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A) @ 
% 0.34/0.53        (k1_relat_1 @ sk_B))),
% 0.34/0.53      inference('demod', [status(thm)], ['14', '33'])).
% 0.34/0.53  thf(t21_funct_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.34/0.53       ( ![C:$i]:
% 0.34/0.53         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.34/0.53           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.34/0.53             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.34/0.53               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X24)
% 0.34/0.53          | ~ (v1_funct_1 @ X24)
% 0.34/0.53          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X24))
% 0.34/0.53          | ~ (r2_hidden @ (k1_funct_1 @ X24 @ X25) @ (k1_relat_1 @ X26))
% 0.34/0.53          | (r2_hidden @ X25 @ (k1_relat_1 @ (k5_relat_1 @ X24 @ X26)))
% 0.34/0.53          | ~ (v1_funct_1 @ X26)
% 0.34/0.53          | ~ (v1_relat_1 @ X26))),
% 0.34/0.53      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.34/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.34/0.53        | (r2_hidden @ sk_A @ 
% 0.34/0.53           (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B)))
% 0.34/0.53        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))
% 0.34/0.53        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.34/0.53        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.34/0.53  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t37_relat_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ A ) =>
% 0.34/0.53       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.34/0.53         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.34/0.53  thf('39', plain,
% 0.34/0.53      (![X19 : $i]:
% 0.34/0.53         (((k2_relat_1 @ X19) = (k1_relat_1 @ (k4_relat_1 @ X19)))
% 0.34/0.53          | ~ (v1_relat_1 @ X19))),
% 0.34/0.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.34/0.53  thf('40', plain,
% 0.34/0.53      (![X19 : $i]:
% 0.34/0.53         (((k1_relat_1 @ X19) = (k2_relat_1 @ (k4_relat_1 @ X19)))
% 0.36/0.53          | ~ (v1_relat_1 @ X19))),
% 0.36/0.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.36/0.53  thf('41', plain,
% 0.36/0.53      (![X19 : $i]:
% 0.36/0.53         (((k2_relat_1 @ X19) = (k1_relat_1 @ (k4_relat_1 @ X19)))
% 0.36/0.53          | ~ (v1_relat_1 @ X19))),
% 0.36/0.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.36/0.53  thf('42', plain,
% 0.36/0.53      (![X19 : $i]:
% 0.36/0.53         (((k1_relat_1 @ X19) = (k2_relat_1 @ (k4_relat_1 @ X19)))
% 0.36/0.53          | ~ (v1_relat_1 @ X19))),
% 0.36/0.53      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.36/0.53  thf(d10_xboole_0, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.53  thf('43', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.53  thf('44', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.36/0.53  thf(d19_relat_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( v1_relat_1 @ B ) =>
% 0.36/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.53  thf('45', plain,
% 0.36/0.53      (![X3 : $i, X4 : $i]:
% 0.36/0.53         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.36/0.53          | (v5_relat_1 @ X3 @ X4)
% 0.36/0.53          | ~ (v1_relat_1 @ X3))),
% 0.36/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.53  thf('46', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.53  thf('47', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v5_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.36/0.53          | ~ (v1_relat_1 @ X0)
% 0.36/0.53          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['42', '46'])).
% 0.36/0.53  thf('48', plain,
% 0.36/0.53      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.36/0.53  thf('49', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (v1_relat_1 @ X0)
% 0.36/0.53          | (v5_relat_1 @ (k4_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.36/0.53      inference('clc', [status(thm)], ['47', '48'])).
% 0.36/0.53  thf('50', plain,
% 0.36/0.53      (![X3 : $i, X4 : $i]:
% 0.36/0.53         (~ (v5_relat_1 @ X3 @ X4)
% 0.36/0.53          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.36/0.53          | ~ (v1_relat_1 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.36/0.54          | (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('clc', [status(thm)], ['51', '52'])).
% 0.36/0.54  thf('54', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 0.36/0.54           (k2_relat_1 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['41', '53'])).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.36/0.54  thf('56', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) @ 
% 0.36/0.54             (k2_relat_1 @ X0)))),
% 0.36/0.54      inference('clc', [status(thm)], ['54', '55'])).
% 0.36/0.54  thf('57', plain,
% 0.36/0.54      (![X0 : $i, X2 : $i]:
% 0.36/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.36/0.54               (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 0.36/0.54          | ((k2_relat_1 @ X0)
% 0.36/0.54              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.54  thf('59', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.36/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.36/0.54          | ((k2_relat_1 @ X0)
% 0.36/0.54              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['40', '58'])).
% 0.36/0.54  thf('60', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ((k2_relat_1 @ X0)
% 0.36/0.54              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 0.36/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['39', '59'])).
% 0.36/0.54  thf('61', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.54      inference('simplify', [status(thm)], ['43'])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ((k2_relat_1 @ X0)
% 0.36/0.54              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 0.36/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.54  thf('63', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.36/0.54          | ((k2_relat_1 @ X0)
% 0.36/0.54              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['62'])).
% 0.36/0.54  thf('64', plain,
% 0.36/0.54      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.36/0.54  thf('65', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | ((k2_relat_1 @ X0)
% 0.36/0.54              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 0.36/0.54      inference('clc', [status(thm)], ['63', '64'])).
% 0.36/0.54  thf('66', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('clc', [status(thm)], ['51', '52'])).
% 0.36/0.54  thf('67', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['65', '66'])).
% 0.36/0.54  thf('68', plain,
% 0.36/0.54      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.36/0.54  thf('69', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.36/0.54      inference('clc', [status(thm)], ['67', '68'])).
% 0.36/0.54  thf('70', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i]:
% 0.36/0.54         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.36/0.54          | (v5_relat_1 @ X3 @ X4)
% 0.36/0.54          | ~ (v1_relat_1 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.54  thf('71', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | ~ (v1_relat_1 @ X0)
% 0.36/0.54          | (v5_relat_1 @ X0 @ (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.54  thf('72', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v5_relat_1 @ X0 @ (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.36/0.54          | ~ (v1_relat_1 @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['71'])).
% 0.36/0.54  thf('73', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t202_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.36/0.54       ( ![C:$i]:
% 0.36/0.54         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.36/0.54  thf('74', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X13 @ (k2_relat_1 @ X14))
% 0.36/0.54          | (r2_hidden @ X13 @ X15)
% 0.36/0.54          | ~ (v5_relat_1 @ X14 @ X15)
% 0.36/0.54          | ~ (v1_relat_1 @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.36/0.54  thf('75', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ sk_B)
% 0.36/0.54          | ~ (v5_relat_1 @ sk_B @ X0)
% 0.36/0.54          | (r2_hidden @ sk_A @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.36/0.54  thf('76', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('77', plain,
% 0.36/0.54      (![X0 : $i]: (~ (v5_relat_1 @ sk_B @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.36/0.54      inference('demod', [status(thm)], ['75', '76'])).
% 0.36/0.54  thf('78', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.36/0.54        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['72', '77'])).
% 0.36/0.54  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('80', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['78', '79'])).
% 0.36/0.54  thf('81', plain,
% 0.36/0.54      (((r2_hidden @ sk_A @ 
% 0.36/0.54         (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B)))
% 0.36/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.36/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['36', '37', '38', '80'])).
% 0.36/0.54  thf('82', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.36/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.36/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.36/0.54        | (r2_hidden @ sk_A @ 
% 0.36/0.54           (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['6', '81'])).
% 0.36/0.54  thf('83', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('84', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('85', plain, ((v2_funct_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('86', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_B))
% 0.36/0.54        | (r2_hidden @ sk_A @ 
% 0.36/0.54           (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B))))),
% 0.36/0.54      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.36/0.54  thf('87', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.36/0.54        | (r2_hidden @ sk_A @ 
% 0.36/0.54           (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['5', '86'])).
% 0.36/0.54  thf('88', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('89', plain,
% 0.36/0.54      ((r2_hidden @ sk_A @ 
% 0.36/0.54        (k1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['87', '88'])).
% 0.36/0.54  thf(t22_funct_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.54       ( ![C:$i]:
% 0.36/0.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.54           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.36/0.54             ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A ) =
% 0.36/0.54               ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ))).
% 0.36/0.54  thf('90', plain,
% 0.36/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X27)
% 0.36/0.54          | ~ (v1_funct_1 @ X27)
% 0.36/0.54          | ((k1_funct_1 @ (k5_relat_1 @ X27 @ X28) @ X29)
% 0.36/0.54              = (k1_funct_1 @ X28 @ (k1_funct_1 @ X27 @ X29)))
% 0.36/0.54          | ~ (r2_hidden @ X29 @ (k1_relat_1 @ (k5_relat_1 @ X27 @ X28)))
% 0.36/0.54          | ~ (v1_funct_1 @ X28)
% 0.36/0.54          | ~ (v1_relat_1 @ X28))),
% 0.36/0.54      inference('cnf', [status(esa)], [t22_funct_1])).
% 0.36/0.54  thf('91', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.36/0.54        | ((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 0.36/0.54            = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))
% 0.36/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.36/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.36/0.54  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('93', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('94', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.36/0.54  thf('95', plain,
% 0.36/0.54      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.36/0.54  thf('96', plain,
% 0.36/0.54      (((sk_A)
% 0.36/0.54         = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k4_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['94', '95'])).
% 0.36/0.54  thf('97', plain,
% 0.36/0.54      ((((k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)
% 0.36/0.54          = (sk_A))
% 0.36/0.54        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.36/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['91', '92', '93', '96'])).
% 0.36/0.54  thf('98', plain,
% 0.36/0.54      (![X20 : $i]:
% 0.36/0.54         (~ (v2_funct_1 @ X20)
% 0.36/0.54          | ((k2_funct_1 @ X20) = (k4_relat_1 @ X20))
% 0.36/0.54          | ~ (v1_funct_1 @ X20)
% 0.36/0.54          | ~ (v1_relat_1 @ X20))),
% 0.36/0.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.36/0.54  thf('99', plain,
% 0.36/0.54      ((((sk_A)
% 0.36/0.54          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))
% 0.36/0.54        | ((sk_A)
% 0.36/0.54            != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('100', plain,
% 0.36/0.54      ((((sk_A)
% 0.36/0.54          != (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((sk_A)
% 0.36/0.54                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.36/0.54                   sk_A))))),
% 0.36/0.54      inference('split', [status(esa)], ['99'])).
% 0.36/0.54  thf('101', plain,
% 0.36/0.54      (((((sk_A)
% 0.36/0.54           != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))
% 0.36/0.54         | ~ (v1_relat_1 @ sk_B)
% 0.36/0.54         | ~ (v1_funct_1 @ sk_B)
% 0.36/0.54         | ~ (v2_funct_1 @ sk_B)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((sk_A)
% 0.36/0.54                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.36/0.54                   sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['98', '100'])).
% 0.36/0.54  thf('102', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('103', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('104', plain, ((v2_funct_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('105', plain,
% 0.36/0.54      ((((sk_A)
% 0.36/0.54          != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((sk_A)
% 0.36/0.54                = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.36/0.54                   sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.36/0.54  thf('106', plain,
% 0.36/0.54      (((sk_D_1 @ sk_A @ sk_B) = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '19', '20', '26', '27'])).
% 0.36/0.54  thf('107', plain,
% 0.36/0.54      ((((sk_A)
% 0.36/0.54          != (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))
% 0.36/0.54         <= (~
% 0.36/0.54             (((sk_A)
% 0.36/0.54                = (k1_funct_1 @ sk_B @ 
% 0.36/0.54                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.36/0.54      inference('split', [status(esa)], ['99'])).
% 0.36/0.54  thf('108', plain,
% 0.36/0.54      ((((sk_A) != (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B))))
% 0.36/0.54         <= (~
% 0.36/0.54             (((sk_A)
% 0.36/0.54                = (k1_funct_1 @ sk_B @ 
% 0.36/0.54                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['106', '107'])).
% 0.36/0.54  thf('109', plain, (((sk_A) = (k1_funct_1 @ sk_B @ (sk_D_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.36/0.54  thf('110', plain,
% 0.36/0.54      ((((sk_A) != (sk_A)))
% 0.36/0.54         <= (~
% 0.36/0.54             (((sk_A)
% 0.36/0.54                = (k1_funct_1 @ sk_B @ 
% 0.36/0.54                   (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A)))))),
% 0.36/0.54      inference('demod', [status(thm)], ['108', '109'])).
% 0.36/0.54  thf('111', plain,
% 0.36/0.54      ((((sk_A)
% 0.36/0.54          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.36/0.54      inference('simplify', [status(thm)], ['110'])).
% 0.36/0.54  thf('112', plain,
% 0.36/0.54      (~
% 0.36/0.54       (((sk_A)
% 0.36/0.54          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A))) | 
% 0.36/0.54       ~
% 0.36/0.54       (((sk_A)
% 0.36/0.54          = (k1_funct_1 @ sk_B @ (k1_funct_1 @ (k2_funct_1 @ sk_B) @ sk_A))))),
% 0.36/0.54      inference('split', [status(esa)], ['99'])).
% 0.36/0.54  thf('113', plain,
% 0.36/0.54      (~
% 0.36/0.54       (((sk_A)
% 0.36/0.54          = (k1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ sk_A)))),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['111', '112'])).
% 0.36/0.54  thf('114', plain,
% 0.36/0.54      (((sk_A)
% 0.36/0.54         != (k1_funct_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_B) @ sk_B) @ sk_A))),
% 0.36/0.54      inference('simpl_trail', [status(thm)], ['105', '113'])).
% 0.36/0.54  thf('115', plain,
% 0.36/0.54      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_B))
% 0.36/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['97', '114'])).
% 0.36/0.54  thf('116', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.36/0.54        | ~ (v2_funct_1 @ sk_B)
% 0.36/0.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '115'])).
% 0.36/0.54  thf('117', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('118', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('119', plain, ((v2_funct_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('120', plain, (~ (v1_relat_1 @ (k4_relat_1 @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.36/0.54  thf('121', plain, (~ (v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '120'])).
% 0.36/0.54  thf('122', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('123', plain, ($false), inference('demod', [status(thm)], ['121', '122'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
