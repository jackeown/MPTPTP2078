%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ff8CIwJpx2

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:54 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 130 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  791 (1615 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t40_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) )
        <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_funct_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

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

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('4',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X4 ) @ X0 )
      | ( X2 != X4 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('18',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X4 ) @ ( k6_relat_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ ( k6_relat_1 @ sk_B ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X15 )
      | ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('23',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ X12 @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('28',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
      | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
      | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X12 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ X8 ) @ X6 )
      | ( X8
       != ( k1_funct_1 @ X6 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( k1_funct_1 @ X6 @ X5 ) ) @ X6 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X10: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('50',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) @ ( k6_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ ( k6_relat_1 @ sk_B ) ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','13','36','37','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ff8CIwJpx2
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:09:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.95  % Solved by: fo/fo7.sh
% 0.76/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.95  % done 444 iterations in 0.482s
% 0.76/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.95  % SZS output start Refutation
% 0.76/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.95  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.76/0.95  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.76/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.95  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.76/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.95  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.76/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.95  thf(t40_funct_1, conjecture,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.76/0.95       ( ( r2_hidden @
% 0.76/0.95           A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) ) <=>
% 0.76/0.95         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.76/0.95           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.76/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.95    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.95        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.76/0.95          ( ( r2_hidden @
% 0.76/0.95              A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) ) <=>
% 0.76/0.95            ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.76/0.95              ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )),
% 0.76/0.95    inference('cnf.neg', [status(esa)], [t40_funct_1])).
% 0.76/0.95  thf('0', plain,
% 0.76/0.95      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.76/0.95        | (r2_hidden @ sk_A @ 
% 0.76/0.95           (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('1', plain,
% 0.76/0.95      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))) | 
% 0.76/0.95       ((r2_hidden @ sk_A @ 
% 0.76/0.95         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))),
% 0.76/0.95      inference('split', [status(esa)], ['0'])).
% 0.76/0.95  thf('2', plain,
% 0.76/0.95      (((r2_hidden @ sk_A @ 
% 0.76/0.95         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ 
% 0.76/0.95               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.76/0.95      inference('split', [status(esa)], ['0'])).
% 0.76/0.95  thf(t21_funct_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.95       ( ![C:$i]:
% 0.76/0.95         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.76/0.95           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.76/0.95             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.76/0.95               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.76/0.95  thf('3', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X11)
% 0.76/0.95          | ~ (v1_funct_1 @ X11)
% 0.76/0.95          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ (k5_relat_1 @ X11 @ X13)))
% 0.76/0.95          | (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.76/0.95          | ~ (v1_funct_1 @ X13)
% 0.76/0.95          | ~ (v1_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.76/0.95  thf('4', plain,
% 0.76/0.95      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.76/0.95         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.76/0.95         | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.76/0.95         | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.95         | ~ (v1_relat_1 @ sk_C_1)))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ 
% 0.76/0.95               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.95  thf(fc3_funct_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.76/0.95       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.76/0.95  thf('5', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('6', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('7', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('8', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('9', plain,
% 0.76/0.95      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ 
% 0.76/0.95               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.76/0.95  thf('10', plain,
% 0.76/0.95      ((~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)
% 0.76/0.95        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.76/0.95        | ~ (r2_hidden @ sk_A @ 
% 0.76/0.95             (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('11', plain,
% 0.76/0.95      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.76/0.95         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))),
% 0.76/0.95      inference('split', [status(esa)], ['10'])).
% 0.76/0.95  thf('12', plain,
% 0.76/0.95      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))) | 
% 0.76/0.95       ~
% 0.76/0.95       ((r2_hidden @ sk_A @ 
% 0.76/0.95         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['9', '11'])).
% 0.76/0.95  thf('13', plain,
% 0.76/0.95      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))) | 
% 0.76/0.95       ~
% 0.76/0.95       ((r2_hidden @ sk_A @ 
% 0.76/0.95         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))) | 
% 0.76/0.95       ~ ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.76/0.95      inference('split', [status(esa)], ['10'])).
% 0.76/0.95  thf('14', plain,
% 0.76/0.95      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))),
% 0.76/0.95      inference('split', [status(esa)], ['0'])).
% 0.76/0.95  thf('15', plain,
% 0.76/0.95      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)
% 0.76/0.95        | (r2_hidden @ sk_A @ 
% 0.76/0.95           (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('16', plain,
% 0.76/0.95      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))
% 0.76/0.95         <= (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['15'])).
% 0.76/0.95  thf(d10_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ B ) =>
% 0.76/0.95       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.76/0.95         ( ![C:$i,D:$i]:
% 0.76/0.95           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.76/0.95             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.76/0.95  thf('17', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.76/0.95         (((X0) != (k6_relat_1 @ X1))
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X2 @ X4) @ X0)
% 0.76/0.95          | ((X2) != (X4))
% 0.76/0.95          | ~ (r2_hidden @ X2 @ X1)
% 0.76/0.95          | ~ (v1_relat_1 @ X0))),
% 0.76/0.95      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.76/0.95  thf('18', plain,
% 0.76/0.95      (![X1 : $i, X4 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.76/0.95          | ~ (r2_hidden @ X4 @ X1)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('simplify', [status(thm)], ['17'])).
% 0.76/0.95  thf('19', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('20', plain,
% 0.76/0.95      (![X1 : $i, X4 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X4 @ X1)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X4 @ X4) @ (k6_relat_1 @ X1)))),
% 0.76/0.95      inference('demod', [status(thm)], ['18', '19'])).
% 0.76/0.95  thf('21', plain,
% 0.76/0.95      (((r2_hidden @ 
% 0.76/0.95         (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.76/0.95          (k1_funct_1 @ sk_C_1 @ sk_A)) @ 
% 0.76/0.95         (k6_relat_1 @ sk_B)))
% 0.76/0.95         <= (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['16', '20'])).
% 0.76/0.95  thf(t8_funct_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.76/0.95       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.76/0.95         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.76/0.95           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.76/0.95  thf('22', plain,
% 0.76/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.76/0.95         (~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X15)
% 0.76/0.95          | (r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.76/0.95          | ~ (v1_funct_1 @ X15)
% 0.76/0.95          | ~ (v1_relat_1 @ X15))),
% 0.76/0.95      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.76/0.95  thf('23', plain,
% 0.76/0.95      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.76/0.95         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.76/0.95         | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.76/0.95            (k1_relat_1 @ (k6_relat_1 @ sk_B)))))
% 0.76/0.95         <= (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.95  thf('24', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('25', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('26', plain,
% 0.76/0.95      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.76/0.95         (k1_relat_1 @ (k6_relat_1 @ sk_B))))
% 0.76/0.95         <= (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.76/0.95  thf('27', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X11)
% 0.76/0.95          | ~ (v1_funct_1 @ X11)
% 0.76/0.95          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.76/0.95          | ~ (r2_hidden @ (k1_funct_1 @ X11 @ X12) @ (k1_relat_1 @ X13))
% 0.76/0.95          | (r2_hidden @ X12 @ (k1_relat_1 @ (k5_relat_1 @ X11 @ X13)))
% 0.76/0.95          | ~ (v1_funct_1 @ X13)
% 0.76/0.95          | ~ (v1_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.76/0.95  thf('28', plain,
% 0.76/0.95      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.76/0.95         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.76/0.95         | (r2_hidden @ sk_A @ 
% 0.76/0.95            (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))
% 0.76/0.95         | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.76/0.95         | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.95         | ~ (v1_relat_1 @ sk_C_1)))
% 0.76/0.95         <= (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['26', '27'])).
% 0.76/0.95  thf('29', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('30', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('31', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('33', plain,
% 0.76/0.95      ((((r2_hidden @ sk_A @ 
% 0.76/0.95          (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))
% 0.76/0.95         | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))))
% 0.76/0.95         <= (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.76/0.95      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.76/0.95  thf('34', plain,
% 0.76/0.95      (((r2_hidden @ sk_A @ 
% 0.76/0.95         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))) & 
% 0.76/0.95             ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['14', '33'])).
% 0.76/0.95  thf('35', plain,
% 0.76/0.95      ((~ (r2_hidden @ sk_A @ 
% 0.76/0.95           (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))
% 0.76/0.95         <= (~
% 0.76/0.95             ((r2_hidden @ sk_A @ 
% 0.76/0.95               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.76/0.95      inference('split', [status(esa)], ['10'])).
% 0.76/0.95  thf('36', plain,
% 0.76/0.95      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))) | 
% 0.76/0.95       ((r2_hidden @ sk_A @ 
% 0.76/0.95         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))) | 
% 0.76/0.95       ~ ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['34', '35'])).
% 0.76/0.95  thf('37', plain,
% 0.76/0.95      (((r2_hidden @ sk_A @ 
% 0.76/0.95         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))) | 
% 0.76/0.95       ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.76/0.95      inference('split', [status(esa)], ['15'])).
% 0.76/0.95  thf('38', plain,
% 0.76/0.95      (((r2_hidden @ sk_A @ 
% 0.76/0.95         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B)))))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ 
% 0.76/0.95               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.76/0.95      inference('split', [status(esa)], ['0'])).
% 0.76/0.95  thf('39', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X11)
% 0.76/0.95          | ~ (v1_funct_1 @ X11)
% 0.76/0.95          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ (k5_relat_1 @ X11 @ X13)))
% 0.76/0.95          | (r2_hidden @ (k1_funct_1 @ X11 @ X12) @ (k1_relat_1 @ X13))
% 0.76/0.95          | ~ (v1_funct_1 @ X13)
% 0.76/0.95          | ~ (v1_relat_1 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.76/0.95  thf('40', plain,
% 0.76/0.95      (((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.76/0.95         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.76/0.95         | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.76/0.95            (k1_relat_1 @ (k6_relat_1 @ sk_B)))
% 0.76/0.95         | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.95         | ~ (v1_relat_1 @ sk_C_1)))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ 
% 0.76/0.95               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.95  thf('41', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('42', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('43', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('45', plain,
% 0.76/0.95      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.76/0.95         (k1_relat_1 @ (k6_relat_1 @ sk_B))))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ 
% 0.76/0.95               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.76/0.95      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.76/0.95  thf(d4_funct_1, axiom,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.95       ( ![B:$i,C:$i]:
% 0.76/0.95         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.76/0.95             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.76/0.95               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.95           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.76/0.95             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.76/0.95               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.76/0.95  thf('46', plain,
% 0.76/0.95      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X5 @ (k1_relat_1 @ X6))
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X5 @ X8) @ X6)
% 0.76/0.95          | ((X8) != (k1_funct_1 @ X6 @ X5))
% 0.76/0.95          | ~ (v1_funct_1 @ X6)
% 0.76/0.95          | ~ (v1_relat_1 @ X6))),
% 0.76/0.95      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.76/0.95  thf('47', plain,
% 0.76/0.95      (![X5 : $i, X6 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ X6)
% 0.76/0.95          | ~ (v1_funct_1 @ X6)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ X5 @ (k1_funct_1 @ X6 @ X5)) @ X6)
% 0.76/0.95          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X6)))),
% 0.76/0.95      inference('simplify', [status(thm)], ['46'])).
% 0.76/0.95  thf('48', plain,
% 0.76/0.95      ((((r2_hidden @ 
% 0.76/0.95          (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.76/0.95           (k1_funct_1 @ (k6_relat_1 @ sk_B) @ (k1_funct_1 @ sk_C_1 @ sk_A))) @ 
% 0.76/0.95          (k6_relat_1 @ sk_B))
% 0.76/0.95         | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B))
% 0.76/0.95         | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ 
% 0.76/0.95               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['45', '47'])).
% 0.76/0.95  thf('49', plain, (![X10 : $i]: (v1_funct_1 @ (k6_relat_1 @ X10))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('50', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('51', plain,
% 0.76/0.95      (((r2_hidden @ 
% 0.76/0.95         (k4_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A) @ 
% 0.76/0.95          (k1_funct_1 @ (k6_relat_1 @ sk_B) @ (k1_funct_1 @ sk_C_1 @ sk_A))) @ 
% 0.76/0.95         (k6_relat_1 @ sk_B)))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ 
% 0.76/0.95               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.76/0.95      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.76/0.95  thf('52', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.95         (((X0) != (k6_relat_1 @ X1))
% 0.76/0.95          | (r2_hidden @ X2 @ X1)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X0)
% 0.76/0.95          | ~ (v1_relat_1 @ X0))),
% 0.76/0.95      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.76/0.95  thf('53', plain,
% 0.76/0.95      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.95         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.76/0.95          | (r2_hidden @ X2 @ X1))),
% 0.76/0.95      inference('simplify', [status(thm)], ['52'])).
% 0.76/0.95  thf('54', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.76/0.95      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.95  thf('55', plain,
% 0.76/0.95      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.95         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ (k6_relat_1 @ X1))
% 0.76/0.95          | (r2_hidden @ X2 @ X1))),
% 0.76/0.95      inference('demod', [status(thm)], ['53', '54'])).
% 0.76/0.95  thf('56', plain,
% 0.76/0.95      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))
% 0.76/0.95         <= (((r2_hidden @ sk_A @ 
% 0.76/0.95               (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['51', '55'])).
% 0.76/0.95  thf('57', plain,
% 0.76/0.95      ((~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))
% 0.76/0.95         <= (~ ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B)))),
% 0.76/0.95      inference('split', [status(esa)], ['10'])).
% 0.76/0.95  thf('58', plain,
% 0.76/0.95      (~
% 0.76/0.95       ((r2_hidden @ sk_A @ 
% 0.76/0.95         (k1_relat_1 @ (k5_relat_1 @ sk_C_1 @ (k6_relat_1 @ sk_B))))) | 
% 0.76/0.95       ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['56', '57'])).
% 0.76/0.95  thf('59', plain, ($false),
% 0.76/0.95      inference('sat_resolution*', [status(thm)],
% 0.76/0.95                ['1', '12', '13', '36', '37', '58'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
