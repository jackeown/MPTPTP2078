%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SCEx1sYQ34

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:47 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 312 expanded)
%              Number of leaves         :   18 (  96 expanded)
%              Depth                    :   21
%              Number of atoms          : 1486 (5263 expanded)
%              Number of equality atoms :   12 (  35 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(t21_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
            <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
                & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_funct_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

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

thf('6',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X13 ) @ X11 )
      | ( X13
       != ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ ( k1_funct_1 @ X11 @ X10 ) ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
       != ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C ) ) @ sk_C )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C ) ) @ sk_C )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C ) ) @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ ( k1_funct_1 @ X11 @ X10 ) ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('42',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ ( k1_funct_1 @ X11 @ X10 ) ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('49',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) @ sk_B )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
       != ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X4 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_B ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ X0 ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) @ ( k5_relat_1 @ X0 @ sk_B ) )
        | ~ ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ X0 ) )
   <= ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) @ ( k5_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) @ ( k5_relat_1 @ sk_C @ sk_B ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('65',plain,
    ( ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
      & ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('77',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('79',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('80',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
       != ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) @ X6 ) @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X6 ) @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X6 @ X3 @ X0 @ X1 ) @ X6 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C ) ) @ sk_C )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('88',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( X18
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('89',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_C @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C )
      = ( k1_funct_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','92'])).

thf('94',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ) ) @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('99',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('104',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','77','78','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SCEx1sYQ34
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 229 iterations in 0.190s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.65  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.46/0.65  thf(t21_funct_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65       ( ![C:$i]:
% 0.46/0.65         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.46/0.65             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.65               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i]:
% 0.46/0.65        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65          ( ![C:$i]:
% 0.46/0.65            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65              ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.46/0.65                ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.65                  ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t21_funct_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.46/0.65        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.46/0.65       ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf(dt_k5_relat_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.46/0.65       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X8)
% 0.46/0.65          | ~ (v1_relat_1 @ X9)
% 0.46/0.65          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X8)
% 0.46/0.65          | ~ (v1_relat_1 @ X9)
% 0.46/0.65          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.46/0.65  thf(fc2_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.46/0.65         ( v1_funct_1 @ B ) ) =>
% 0.46/0.65       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.46/0.65         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         (~ (v1_funct_1 @ X14)
% 0.46/0.65          | ~ (v1_relat_1 @ X14)
% 0.46/0.65          | ~ (v1_relat_1 @ X15)
% 0.46/0.65          | ~ (v1_funct_1 @ X15)
% 0.46/0.65          | (v1_funct_1 @ (k5_relat_1 @ X14 @ X15)))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf(d4_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ![B:$i,C:$i]:
% 0.46/0.65         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.65             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.46/0.65               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.65           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.46/0.65             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.46/0.65               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X10 @ X13) @ X11)
% 0.46/0.65          | ((X13) != (k1_funct_1 @ X11 @ X10))
% 0.46/0.65          | ~ (v1_funct_1 @ X11)
% 0.46/0.65          | ~ (v1_relat_1 @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X11)
% 0.46/0.65          | ~ (v1_funct_1 @ X11)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X10 @ (k1_funct_1 @ X11 @ X10)) @ X11)
% 0.46/0.65          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      ((((r2_hidden @ 
% 0.46/0.65          (k4_tarski @ sk_A @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65          (k5_relat_1 @ sk_C @ sk_B))
% 0.46/0.65         | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 0.46/0.65         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['5', '7'])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (((~ (v1_funct_1 @ sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65         | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 0.46/0.65         | (r2_hidden @ 
% 0.46/0.65            (k4_tarski @ sk_A @ 
% 0.46/0.65             (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65            (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '8'])).
% 0.46/0.65  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 0.46/0.65         | (r2_hidden @ 
% 0.46/0.65            (k4_tarski @ sk_A @ 
% 0.46/0.65             (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65            (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65         | (r2_hidden @ 
% 0.46/0.65            (k4_tarski @ sk_A @ 
% 0.46/0.65             (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65            (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '14'])).
% 0.46/0.65  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (((r2_hidden @ 
% 0.46/0.65         (k4_tarski @ sk_A @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65         (k5_relat_1 @ sk_C @ sk_B)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.46/0.65  thf(d8_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( v1_relat_1 @ B ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( v1_relat_1 @ C ) =>
% 0.46/0.65               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.46/0.65                 ( ![D:$i,E:$i]:
% 0.46/0.65                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.46/0.65                     ( ?[F:$i]:
% 0.46/0.65                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.46/0.65                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X6 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((X2) != (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ (sk_F_1 @ X6 @ X3 @ X0 @ X1)) @ X1)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X6) @ X2)
% 0.46/0.65          | ~ (v1_relat_1 @ X2)
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X3 : $i, X6 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X1)
% 0.46/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X6) @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ (sk_F_1 @ X6 @ X3 @ X0 @ X1)) @ X1)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ sk_B)
% 0.46/0.65         | (r2_hidden @ 
% 0.46/0.65            (k4_tarski @ sk_A @ 
% 0.46/0.65             (sk_F_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.46/0.65              sk_A @ sk_B @ sk_C)) @ 
% 0.46/0.65            sk_C)
% 0.46/0.65         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['18', '20'])).
% 0.46/0.65  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      ((((r2_hidden @ 
% 0.46/0.65          (k4_tarski @ sk_A @ 
% 0.46/0.65           (sk_F_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A) @ sk_A @ 
% 0.46/0.65            sk_B @ sk_C)) @ 
% 0.46/0.65          sk_C)
% 0.46/0.65         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65         | (r2_hidden @ 
% 0.46/0.65            (k4_tarski @ sk_A @ 
% 0.46/0.65             (sk_F_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.46/0.65              sk_A @ sk_B @ sk_C)) @ 
% 0.46/0.65            sk_C)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '24'])).
% 0.46/0.65  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (((r2_hidden @ 
% 0.46/0.65         (k4_tarski @ sk_A @ 
% 0.46/0.65          (sk_F_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A) @ sk_A @ 
% 0.46/0.65           sk_B @ sk_C)) @ 
% 0.46/0.65         sk_C))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.46/0.65  thf(t8_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.46/0.65         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.65           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.46/0.65          | (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.46/0.65          | ~ (v1_funct_1 @ X17)
% 0.46/0.65          | ~ (v1_relat_1 @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ sk_C)
% 0.46/0.65         | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65         | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      ((~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.46/0.65        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.46/0.65        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.46/0.65         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.46/0.65      inference('split', [status(esa)], ['34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.46/0.65       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['33', '35'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.46/0.65       ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))) | 
% 0.46/0.65       ~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.46/0.65      inference('split', [status(esa)], ['34'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         (~ (v1_funct_1 @ X14)
% 0.46/0.65          | ~ (v1_relat_1 @ X14)
% 0.46/0.65          | ~ (v1_relat_1 @ X15)
% 0.46/0.65          | ~ (v1_funct_1 @ X15)
% 0.46/0.65          | (v1_funct_1 @ (k5_relat_1 @ X14 @ X15)))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X8)
% 0.46/0.65          | ~ (v1_relat_1 @ X9)
% 0.46/0.65          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X11)
% 0.46/0.65          | ~ (v1_funct_1 @ X11)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X10 @ (k1_funct_1 @ X11 @ X10)) @ X11)
% 0.46/0.65          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      ((((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)
% 0.46/0.65         | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.65  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))),
% 0.46/0.65      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.46/0.65        | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.46/0.65         <= (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('split', [status(esa)], ['46'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X11)
% 0.46/0.65          | ~ (v1_funct_1 @ X11)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X10 @ (k1_funct_1 @ X11 @ X10)) @ X11)
% 0.46/0.65          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      ((((r2_hidden @ 
% 0.46/0.65          (k4_tarski @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.46/0.65           (k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_C @ sk_A))) @ 
% 0.46/0.65          sk_B)
% 0.46/0.65         | ~ (v1_funct_1 @ sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ sk_B)))
% 0.46/0.65         <= (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.65  thf('50', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (((r2_hidden @ 
% 0.46/0.65         (k4_tarski @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.46/0.65          (k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_C @ sk_A))) @ 
% 0.46/0.65         sk_B))
% 0.46/0.65         <= (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X8)
% 0.46/0.65          | ~ (v1_relat_1 @ X9)
% 0.46/0.65          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((X2) != (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X1)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X5 @ X4) @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X2)
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X1)
% 0.46/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X5 @ X4) @ X0)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X1)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['54'])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X1)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X0)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X1)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      ((![X0 : $i, X1 : $i]:
% 0.46/0.65          (~ (v1_relat_1 @ sk_B)
% 0.46/0.65           | ~ (v1_relat_1 @ X0)
% 0.46/0.65           | (r2_hidden @ 
% 0.46/0.65              (k4_tarski @ X1 @ 
% 0.46/0.65               (k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_C @ sk_A))) @ 
% 0.46/0.65              (k5_relat_1 @ X0 @ sk_B))
% 0.46/0.65           | ~ (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ sk_C @ sk_A)) @ X0)))
% 0.46/0.65         <= (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['52', '57'])).
% 0.46/0.65  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      ((![X0 : $i, X1 : $i]:
% 0.46/0.65          (~ (v1_relat_1 @ X0)
% 0.46/0.65           | (r2_hidden @ 
% 0.46/0.65              (k4_tarski @ X1 @ 
% 0.46/0.65               (k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_C @ sk_A))) @ 
% 0.46/0.65              (k5_relat_1 @ X0 @ sk_B))
% 0.46/0.65           | ~ (r2_hidden @ (k4_tarski @ X1 @ (k1_funct_1 @ sk_C @ sk_A)) @ X0)))
% 0.46/0.65         <= (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['58', '59'])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      ((((r2_hidden @ 
% 0.46/0.65          (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_C @ sk_A))) @ 
% 0.46/0.65          (k5_relat_1 @ sk_C @ sk_B))
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.46/0.65             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['45', '60'])).
% 0.46/0.65  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (((r2_hidden @ 
% 0.46/0.65         (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ (k1_funct_1 @ sk_C @ sk_A))) @ 
% 0.46/0.65         (k5_relat_1 @ sk_C @ sk_B)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.46/0.65             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['61', '62'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.46/0.65          | (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.46/0.65          | ~ (v1_funct_1 @ X17)
% 0.46/0.65          | ~ (v1_relat_1 @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 0.46/0.65         | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 0.46/0.65         | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.46/0.65             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65         | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))
% 0.46/0.65         | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.46/0.65             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '65'])).
% 0.46/0.65  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      ((((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))
% 0.46/0.65         | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.46/0.65             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (((~ (v1_funct_1 @ sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65         | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65         | (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.46/0.65             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['38', '69'])).
% 0.46/0.65  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) & 
% 0.46/0.65             ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['70', '71', '72', '73', '74'])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('split', [status(esa)], ['34'])).
% 0.46/0.65  thf('77', plain,
% 0.46/0.65      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))) | 
% 0.46/0.65       ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))) | 
% 0.46/0.65       ~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))) | 
% 0.46/0.65       ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.46/0.65      inference('split', [status(esa)], ['46'])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X8)
% 0.46/0.65          | ~ (v1_relat_1 @ X9)
% 0.46/0.65          | (v1_relat_1 @ (k5_relat_1 @ X8 @ X9)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (((r2_hidden @ 
% 0.46/0.65         (k4_tarski @ sk_A @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65         (k5_relat_1 @ sk_C @ sk_B)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.46/0.65  thf('81', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X6 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((X2) != (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X6 @ X3 @ X0 @ X1) @ X6) @ X0)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X6) @ X2)
% 0.46/0.65          | ~ (v1_relat_1 @ X2)
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.46/0.65  thf('82', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X3 : $i, X6 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X1)
% 0.46/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X3 @ X6) @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.65          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X6 @ X3 @ X0 @ X1) @ X6) @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['81'])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ sk_B)
% 0.46/0.65         | (r2_hidden @ 
% 0.46/0.65            (k4_tarski @ 
% 0.46/0.65             (sk_F_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.46/0.65              sk_A @ sk_B @ sk_C) @ 
% 0.46/0.65             (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65            sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['80', '82'])).
% 0.46/0.65  thf('84', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      ((((r2_hidden @ 
% 0.46/0.65          (k4_tarski @ 
% 0.46/0.65           (sk_F_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A) @ sk_A @ 
% 0.46/0.65            sk_B @ sk_C) @ 
% 0.46/0.65           (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65          sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.46/0.65  thf('87', plain,
% 0.46/0.65      (((r2_hidden @ 
% 0.46/0.65         (k4_tarski @ sk_A @ 
% 0.46/0.65          (sk_F_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A) @ sk_A @ 
% 0.46/0.65           sk_B @ sk_C)) @ 
% 0.46/0.65         sk_C))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.46/0.65          | ((X18) = (k1_funct_1 @ X17 @ X16))
% 0.46/0.65          | ~ (v1_funct_1 @ X17)
% 0.46/0.65          | ~ (v1_relat_1 @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.65  thf('89', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ sk_C)
% 0.46/0.65         | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65         | ((sk_F_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.46/0.65             sk_A @ sk_B @ sk_C) = (k1_funct_1 @ sk_C @ sk_A))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.65  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('92', plain,
% 0.46/0.65      ((((sk_F_1 @ (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A) @ sk_A @ 
% 0.46/0.65          sk_B @ sk_C) = (k1_funct_1 @ sk_C @ sk_A)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      ((((r2_hidden @ 
% 0.46/0.65          (k4_tarski @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.46/0.65           (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65          sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['86', '92'])).
% 0.46/0.65  thf('94', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ sk_B)
% 0.46/0.65         | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65         | (r2_hidden @ 
% 0.46/0.65            (k4_tarski @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.46/0.65             (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65            sk_B)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['79', '93'])).
% 0.46/0.65  thf('95', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('97', plain,
% 0.46/0.65      (((r2_hidden @ 
% 0.46/0.65         (k4_tarski @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.46/0.65          (k1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)) @ 
% 0.46/0.65         sk_B))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.46/0.65  thf('98', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.46/0.65          | (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.46/0.65          | ~ (v1_funct_1 @ X17)
% 0.46/0.65          | ~ (v1_relat_1 @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.65  thf('99', plain,
% 0.46/0.65      (((~ (v1_relat_1 @ sk_B)
% 0.46/0.65         | ~ (v1_funct_1 @ sk_B)
% 0.46/0.65         | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['97', '98'])).
% 0.46/0.65  thf('100', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('101', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('102', plain,
% 0.46/0.65      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.46/0.65      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.46/0.65  thf('103', plain,
% 0.46/0.65      ((~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.46/0.65         <= (~ ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.46/0.65      inference('split', [status(esa)], ['34'])).
% 0.46/0.65  thf('104', plain,
% 0.46/0.65      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))) | 
% 0.46/0.65       ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['102', '103'])).
% 0.46/0.65  thf('105', plain, ($false),
% 0.46/0.65      inference('sat_resolution*', [status(thm)],
% 0.46/0.65                ['1', '36', '37', '77', '78', '104'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
