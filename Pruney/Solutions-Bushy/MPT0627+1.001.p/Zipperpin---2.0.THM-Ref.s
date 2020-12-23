%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0627+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1z2ygkCQhu

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:13 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 783 expanded)
%              Number of leaves         :   18 ( 235 expanded)
%              Depth                    :   24
%              Number of atoms          :  974 (13111 expanded)
%              Number of equality atoms :   37 ( 458 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(t22_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
              = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
             => ( ( k1_funct_1 @ ( k5_relat_1 @ C @ B ) @ A )
                = ( k1_funct_1 @ B @ ( k1_funct_1 @ C @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_funct_1])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('4',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ( X3
       != ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

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

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) @ X17 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('24',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( X13
       != ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X14: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X17 ) @ ( k5_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_F_1 @ X17 @ X14 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32','33'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ( X0
        = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
      | ( X0
        = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( sk_F_1 @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','44'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('52',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) @ sk_B )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) @ sk_B )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X2
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ( X2 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( X2
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) @ sk_B )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','69'])).

thf('71',plain,
    ( ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','70'])).

thf('72',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_B @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('74',plain,(
    ( k1_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','74'])).


%------------------------------------------------------------------------------
