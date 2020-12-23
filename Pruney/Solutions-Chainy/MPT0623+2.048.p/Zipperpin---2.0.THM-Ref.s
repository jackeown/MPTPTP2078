%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UGGdUdbGU5

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:42 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 179 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  747 (1651 expanded)
%              Number of equality atoms :   92 ( 206 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_4 @ X19 @ X20 ) )
        = X20 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_relat_1 @ ( sk_C_4 @ X19 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_1 @ ( sk_C_4 @ X19 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_4 @ X19 @ X20 ) )
        = ( k1_tarski @ X19 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('13',plain,(
    ! [X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ sk_A @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C_1 @ sk_A @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ sk_A @ X0 ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ sk_A @ X1 ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ sk_A @ X1 ) @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X1 ) @ X1 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X1 ) @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ sk_A @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ sk_A @ X1 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ sk_A @ X1 ) @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X1 ) @ X1 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X1 ) @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_1 @ sk_A @ X1 ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X1 ) @ X1 )
      | ( X1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    ! [X1: $i] :
      ( ( X1 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X1 ) @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('22',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X16 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( sk_B_1
     != ( k1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('32',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('33',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('34',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( X1 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X1 ) @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','34'])).

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

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_2 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ( ( sk_C_2 @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ( ( sk_C_2 @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X2 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_2 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_2 @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('57',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup-',[status(thm)],['35','60'])).

thf('62',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('65',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('66',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['63','69'])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UGGdUdbGU5
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.63  % Solved by: fo/fo7.sh
% 0.39/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.63  % done 325 iterations in 0.175s
% 0.39/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.63  % SZS output start Refutation
% 0.39/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.39/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.63  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 0.39/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.63  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.39/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.63  thf(t15_funct_1, axiom,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.39/0.63       ( ![B:$i]:
% 0.39/0.63         ( ?[C:$i]:
% 0.39/0.63           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.39/0.63             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.39/0.63             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.39/0.63  thf('0', plain,
% 0.39/0.63      (![X19 : $i, X20 : $i]:
% 0.39/0.63         (((k1_relat_1 @ (sk_C_4 @ X19 @ X20)) = (X20))
% 0.39/0.63          | ((X20) = (k1_xboole_0)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.39/0.63  thf('1', plain,
% 0.39/0.63      (![X19 : $i, X20 : $i]:
% 0.39/0.63         ((v1_relat_1 @ (sk_C_4 @ X19 @ X20)) | ((X20) = (k1_xboole_0)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.39/0.63  thf('2', plain,
% 0.39/0.63      (![X19 : $i, X20 : $i]:
% 0.39/0.63         ((v1_funct_1 @ (sk_C_4 @ X19 @ X20)) | ((X20) = (k1_xboole_0)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.39/0.63  thf(t2_tarski, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.39/0.63       ( ( A ) = ( B ) ) ))).
% 0.39/0.63  thf('3', plain,
% 0.39/0.63      (![X4 : $i, X5 : $i]:
% 0.39/0.63         (((X5) = (X4))
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.39/0.63      inference('cnf', [status(esa)], [t2_tarski])).
% 0.39/0.63  thf(d3_tarski, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.63  thf('4', plain,
% 0.39/0.63      (![X1 : $i, X3 : $i]:
% 0.39/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.63  thf(d1_tarski, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.63  thf('5', plain,
% 0.39/0.63      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X14 @ X13)
% 0.39/0.63          | ((X14) = (X11))
% 0.39/0.63          | ((X13) != (k1_tarski @ X11)))),
% 0.39/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.63  thf('6', plain,
% 0.39/0.63      (![X11 : $i, X14 : $i]:
% 0.39/0.63         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.63  thf('7', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.39/0.63          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.63  thf('8', plain,
% 0.39/0.63      (![X1 : $i, X3 : $i]:
% 0.39/0.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.63  thf('9', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.63          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.39/0.63          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.39/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.63  thf('10', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.39/0.63      inference('simplify', [status(thm)], ['9'])).
% 0.39/0.63  thf('11', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1)
% 0.39/0.63          | ((X1) = (X0))
% 0.39/0.63          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X0 @ X1)) @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['3', '10'])).
% 0.39/0.63  thf('12', plain,
% 0.39/0.63      (![X19 : $i, X20 : $i]:
% 0.39/0.63         (((k2_relat_1 @ (sk_C_4 @ X19 @ X20)) = (k1_tarski @ X19))
% 0.39/0.63          | ((X20) = (k1_xboole_0)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.39/0.63  thf(t18_funct_1, conjecture,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.63          ( ![C:$i]:
% 0.39/0.63            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.63              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.39/0.63                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.39/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.63    (~( ![A:$i,B:$i]:
% 0.39/0.63        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.63             ( ![C:$i]:
% 0.39/0.63               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.63                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.39/0.63                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.39/0.63    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.39/0.63  thf('13', plain,
% 0.39/0.63      (![X21 : $i]:
% 0.39/0.63         (~ (r1_tarski @ (k2_relat_1 @ X21) @ sk_A)
% 0.39/0.63          | ((sk_B_1) != (k1_relat_1 @ X21))
% 0.39/0.63          | ~ (v1_funct_1 @ X21)
% 0.39/0.63          | ~ (v1_relat_1 @ X21))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('14', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.39/0.63          | ((X1) = (k1_xboole_0))
% 0.39/0.63          | ~ (v1_relat_1 @ (sk_C_4 @ X0 @ X1))
% 0.39/0.63          | ~ (v1_funct_1 @ (sk_C_4 @ X0 @ X1))
% 0.39/0.63          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ X0 @ X1))))),
% 0.39/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.63  thf('15', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (((X0) = (sk_A))
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ sk_A @ X0) @ X0)
% 0.39/0.63          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C_1 @ sk_A @ X0) @ X1)))
% 0.39/0.63          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C_1 @ sk_A @ X0) @ X1))
% 0.39/0.63          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_1 @ sk_A @ X0) @ X1))
% 0.39/0.63          | ((X1) = (k1_xboole_0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['11', '14'])).
% 0.39/0.63  thf('16', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (((X0) = (k1_xboole_0))
% 0.39/0.63          | ((X0) = (k1_xboole_0))
% 0.39/0.63          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_1 @ sk_A @ X1) @ X0))
% 0.39/0.63          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C_1 @ sk_A @ X1) @ X0)))
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ sk_A @ X1) @ X1)
% 0.39/0.63          | ((X1) = (sk_A)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['2', '15'])).
% 0.39/0.63  thf('17', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (((X1) = (sk_A))
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ sk_A @ X1) @ X1)
% 0.39/0.63          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C_1 @ sk_A @ X1) @ X0)))
% 0.39/0.63          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_1 @ sk_A @ X1) @ X0))
% 0.39/0.63          | ((X0) = (k1_xboole_0)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.63  thf('18', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (((X0) = (k1_xboole_0))
% 0.39/0.63          | ((X0) = (k1_xboole_0))
% 0.39/0.63          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C_1 @ sk_A @ X1) @ X0)))
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ sk_A @ X1) @ X1)
% 0.39/0.63          | ((X1) = (sk_A)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['1', '17'])).
% 0.39/0.63  thf('19', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (((X1) = (sk_A))
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ sk_A @ X1) @ X1)
% 0.39/0.63          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ (sk_C_1 @ sk_A @ X1) @ X0)))
% 0.39/0.63          | ((X0) = (k1_xboole_0)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['18'])).
% 0.39/0.63  thf('20', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (((sk_B_1) != (X0))
% 0.39/0.63          | ((X0) = (k1_xboole_0))
% 0.39/0.63          | ((X0) = (k1_xboole_0))
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ sk_A @ X1) @ X1)
% 0.39/0.63          | ((X1) = (sk_A)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['0', '19'])).
% 0.39/0.63  thf('21', plain,
% 0.39/0.63      (![X1 : $i]:
% 0.39/0.63         (((X1) = (sk_A))
% 0.39/0.63          | (r2_hidden @ (sk_C_1 @ sk_A @ X1) @ X1)
% 0.39/0.63          | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['20'])).
% 0.39/0.63  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ?[B:$i]:
% 0.39/0.63       ( ( ![C:$i]:
% 0.39/0.63           ( ( r2_hidden @ C @ A ) =>
% 0.39/0.63             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.63         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.39/0.63         ( v1_relat_1 @ B ) ) ))).
% 0.39/0.63  thf('22', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.39/0.63      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.39/0.63  thf(t65_relat_1, axiom,
% 0.39/0.63    (![A:$i]:
% 0.39/0.63     ( ( v1_relat_1 @ A ) =>
% 0.39/0.63       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.63         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.63  thf('23', plain,
% 0.39/0.63      (![X16 : $i]:
% 0.39/0.63         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 0.39/0.63          | ((k2_relat_1 @ X16) = (k1_xboole_0))
% 0.39/0.63          | ~ (v1_relat_1 @ X16))),
% 0.39/0.63      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.39/0.63  thf('24', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (((X0) != (k1_xboole_0))
% 0.39/0.63          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.39/0.63          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.63  thf('25', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.39/0.63      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.39/0.63  thf('26', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (((X0) != (k1_xboole_0))
% 0.39/0.63          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.39/0.63      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.63  thf('27', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.39/0.63      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.63  thf('28', plain,
% 0.39/0.63      (![X21 : $i]:
% 0.39/0.63         (~ (r1_tarski @ (k2_relat_1 @ X21) @ sk_A)
% 0.39/0.63          | ((sk_B_1) != (k1_relat_1 @ X21))
% 0.39/0.63          | ~ (v1_funct_1 @ X21)
% 0.39/0.63          | ~ (v1_relat_1 @ X21))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('29', plain,
% 0.39/0.63      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.39/0.63        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.39/0.63        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 0.39/0.63        | ((sk_B_1) != (k1_relat_1 @ (sk_B @ k1_xboole_0))))),
% 0.39/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.63  thf('30', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.39/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.63  thf('31', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.39/0.63      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.39/0.63  thf('32', plain, (![X17 : $i]: (v1_funct_1 @ (sk_B @ X17))),
% 0.39/0.63      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.39/0.63  thf('33', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.39/0.63      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.39/0.63  thf('34', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.39/0.63      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.39/0.63  thf('35', plain,
% 0.39/0.63      (![X1 : $i]: (((X1) = (sk_A)) | (r2_hidden @ (sk_C_1 @ sk_A @ X1) @ X1))),
% 0.39/0.63      inference('simplify_reflect-', [status(thm)], ['21', '34'])).
% 0.39/0.63  thf(t3_xboole_0, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.63            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.63       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.63            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.63  thf('36', plain,
% 0.39/0.63      (![X6 : $i, X7 : $i]:
% 0.39/0.63         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_2 @ X7 @ X6) @ X6))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.63  thf('37', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.39/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.63  thf('38', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.63          | (r2_hidden @ X0 @ X2)
% 0.39/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.39/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.63  thf('39', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.63  thf('40', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.63          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X1))),
% 0.39/0.63      inference('sup-', [status(thm)], ['36', '39'])).
% 0.39/0.63  thf('41', plain,
% 0.39/0.63      (![X11 : $i, X14 : $i]:
% 0.39/0.63         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.63  thf('42', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.39/0.63          | ((sk_C_2 @ X1 @ k1_xboole_0) = (X0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.63  thf('43', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.39/0.63          | ((sk_C_2 @ X1 @ k1_xboole_0) = (X0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.63  thf('44', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.63         (((X0) = (X1))
% 0.39/0.63          | (r1_xboole_0 @ k1_xboole_0 @ X2)
% 0.39/0.63          | (r1_xboole_0 @ k1_xboole_0 @ X2))),
% 0.39/0.63      inference('sup+', [status(thm)], ['42', '43'])).
% 0.39/0.63  thf('45', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.63         ((r1_xboole_0 @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['44'])).
% 0.39/0.63  thf('46', plain,
% 0.39/0.63      (![X6 : $i, X7 : $i]:
% 0.39/0.63         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_2 @ X7 @ X6) @ X6))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.63  thf('47', plain,
% 0.39/0.63      (![X6 : $i, X7 : $i]:
% 0.39/0.63         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_2 @ X7 @ X6) @ X7))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.63  thf('48', plain,
% 0.39/0.63      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X8 @ X6)
% 0.39/0.63          | ~ (r2_hidden @ X8 @ X9)
% 0.39/0.63          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.63  thf('49', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.63         ((r1_xboole_0 @ X1 @ X0)
% 0.39/0.63          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.39/0.63          | ~ (r2_hidden @ (sk_C_2 @ X0 @ X1) @ X2))),
% 0.39/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.39/0.63  thf('50', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((r1_xboole_0 @ X0 @ X1)
% 0.39/0.63          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.39/0.63          | (r1_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('sup-', [status(thm)], ['46', '49'])).
% 0.39/0.63  thf('51', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.39/0.63      inference('simplify', [status(thm)], ['50'])).
% 0.39/0.63  thf('52', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.63         (((X1) = (X2)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['45', '51'])).
% 0.39/0.63  thf('53', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.39/0.63      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.39/0.63  thf('54', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (((sk_B_1) != (X0)) | (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.39/0.63  thf('55', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.39/0.63      inference('simplify', [status(thm)], ['54'])).
% 0.39/0.63  thf('56', plain,
% 0.39/0.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.63         (((X12) != (X11))
% 0.39/0.63          | (r2_hidden @ X12 @ X13)
% 0.39/0.63          | ((X13) != (k1_tarski @ X11)))),
% 0.39/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.63  thf('57', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_tarski @ X11))),
% 0.39/0.63      inference('simplify', [status(thm)], ['56'])).
% 0.39/0.63  thf('58', plain,
% 0.39/0.63      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.39/0.63         (~ (r2_hidden @ X8 @ X6)
% 0.39/0.63          | ~ (r2_hidden @ X8 @ X9)
% 0.39/0.63          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.63  thf('59', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.39/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.63  thf('60', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.63      inference('sup-', [status(thm)], ['55', '59'])).
% 0.39/0.63  thf('61', plain, (((k1_xboole_0) = (sk_A))),
% 0.39/0.63      inference('sup-', [status(thm)], ['35', '60'])).
% 0.39/0.63  thf('62', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('63', plain,
% 0.39/0.63      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.39/0.63      inference('split', [status(esa)], ['62'])).
% 0.39/0.63  thf('64', plain,
% 0.39/0.63      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.39/0.63      inference('split', [status(esa)], ['62'])).
% 0.39/0.63  thf('65', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.39/0.63      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.39/0.63  thf('66', plain,
% 0.39/0.63      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.39/0.63      inference('sup-', [status(thm)], ['64', '65'])).
% 0.39/0.63  thf('67', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['66'])).
% 0.39/0.63  thf('68', plain,
% 0.39/0.63      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.63      inference('split', [status(esa)], ['62'])).
% 0.39/0.63  thf('69', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.39/0.63      inference('sat_resolution*', [status(thm)], ['67', '68'])).
% 0.39/0.63  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 0.39/0.63      inference('simpl_trail', [status(thm)], ['63', '69'])).
% 0.39/0.63  thf('71', plain, ($false),
% 0.39/0.63      inference('simplify_reflect-', [status(thm)], ['61', '70'])).
% 0.39/0.63  
% 0.39/0.63  % SZS output end Refutation
% 0.39/0.63  
% 0.49/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
