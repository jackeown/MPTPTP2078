%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z0o69onPcw

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:34 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 368 expanded)
%              Number of leaves         :   19 ( 114 expanded)
%              Depth                    :   24
%              Number of atoms          :  912 (4827 expanded)
%              Number of equality atoms :   31 ( 144 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf('0',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( X13 = k1_xboole_0 )
      | ( X13
       != ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k1_funct_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t175_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B )
            & ( v5_funct_1 @ B @ A ) )
         => ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B )
              & ( v5_funct_1 @ B @ A ) )
           => ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_1])).

thf('4',plain,(
    v5_funct_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v5_funct_1 @ X8 @ X9 )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X10 ) @ ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_funct_1 @ X2 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v5_funct_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) ) )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) ) @ ( k1_funct_1 @ sk_A @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_C @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    v5_funct_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k1_funct_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v5_funct_1 @ X8 @ X9 )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X10 ) @ ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k1_funct_1 @ X2 @ X1 ) )
      | ~ ( v5_funct_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v5_funct_1 @ X0 @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k1_funct_1 @ X2 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k1_funct_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k1_funct_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) ) @ k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) ) @ k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( sk_C_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_relat_1 @ sk_A ) )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('39',plain,(
    ! [X1: $i] :
      ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ X1 ) )
        = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ X12 )
      | ( X14
       != ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( k1_funct_1 @ X12 @ X11 ) ) @ X12 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 ) @ sk_B ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k1_funct_1 @ X12 @ X11 )
        = k1_xboole_0 )
      | ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('52',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( X14
        = ( k1_funct_1 @ X12 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( X2
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_C @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','59','60','61'])).

thf('63',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) )
    | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['35'])).

thf('69',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z0o69onPcw
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 255 iterations in 0.178s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.44/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.44/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.63  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.44/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.63  thf(d4_funct_1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.63       ( ![B:$i,C:$i]:
% 0.44/0.63         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.44/0.63             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.44/0.63               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.63           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.44/0.63             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.44/0.63               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.44/0.63  thf('0', plain,
% 0.44/0.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.63         ((r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.44/0.63          | ((X13) = (k1_xboole_0))
% 0.44/0.63          | ((X13) != (k1_funct_1 @ X12 @ X11))
% 0.44/0.63          | ~ (v1_funct_1 @ X12)
% 0.44/0.63          | ~ (v1_relat_1 @ X12))),
% 0.44/0.63      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      (![X11 : $i, X12 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X12)
% 0.44/0.63          | ~ (v1_funct_1 @ X12)
% 0.44/0.63          | ((k1_funct_1 @ X12 @ X11) = (k1_xboole_0))
% 0.44/0.63          | (r2_hidden @ X11 @ (k1_relat_1 @ X12)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['0'])).
% 0.44/0.63  thf(d3_tarski, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      (![X1 : $i, X3 : $i]:
% 0.44/0.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.63  thf('3', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((k1_funct_1 @ X0 @ (sk_C @ (k1_relat_1 @ X0) @ X1)) = (k1_xboole_0))
% 0.44/0.63          | ~ (v1_funct_1 @ X0)
% 0.44/0.63          | ~ (v1_relat_1 @ X0)
% 0.44/0.63          | (r1_tarski @ X1 @ (k1_relat_1 @ X0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.63  thf(t175_funct_1, conjecture,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & ( v5_funct_1 @ B @ A ) ) =>
% 0.44/0.63           ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i]:
% 0.44/0.63        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.63          ( ![B:$i]:
% 0.44/0.63            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & 
% 0.44/0.63                ( v5_funct_1 @ B @ A ) ) =>
% 0.44/0.63              ( r1_tarski @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t175_funct_1])).
% 0.44/0.63  thf('4', plain, ((v5_funct_1 @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('5', plain,
% 0.44/0.63      (![X1 : $i, X3 : $i]:
% 0.44/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.63  thf(d20_funct_1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.63           ( ( v5_funct_1 @ B @ A ) <=>
% 0.44/0.63             ( ![C:$i]:
% 0.44/0.63               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.44/0.63                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf('6', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X8)
% 0.44/0.63          | ~ (v1_funct_1 @ X8)
% 0.44/0.63          | ~ (v5_funct_1 @ X8 @ X9)
% 0.44/0.63          | (r2_hidden @ (k1_funct_1 @ X8 @ X10) @ (k1_funct_1 @ X9 @ X10))
% 0.44/0.63          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X8))
% 0.44/0.63          | ~ (v1_funct_1 @ X9)
% 0.44/0.63          | ~ (v1_relat_1 @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.44/0.63  thf('7', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.44/0.63          | ~ (v1_relat_1 @ X2)
% 0.44/0.63          | ~ (v1_funct_1 @ X2)
% 0.44/0.63          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0))) @ 
% 0.44/0.63             (k1_funct_1 @ X2 @ (sk_C @ X1 @ (k1_relat_1 @ X0))))
% 0.44/0.63          | ~ (v5_funct_1 @ X0 @ X2)
% 0.44/0.63          | ~ (v1_funct_1 @ X0)
% 0.44/0.63          | ~ (v1_relat_1 @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.63  thf('8', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ sk_B)
% 0.44/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.44/0.63          | (r2_hidden @ 
% 0.44/0.63             (k1_funct_1 @ sk_B @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))) @ 
% 0.44/0.63             (k1_funct_1 @ sk_A @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))))
% 0.44/0.63          | ~ (v1_funct_1 @ sk_A)
% 0.44/0.63          | ~ (v1_relat_1 @ sk_A)
% 0.44/0.63          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['4', '7'])).
% 0.44/0.63  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('11', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('13', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         ((r2_hidden @ 
% 0.44/0.63           (k1_funct_1 @ sk_B @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))) @ 
% 0.44/0.63           (k1_funct_1 @ sk_A @ (sk_C @ X0 @ (k1_relat_1 @ sk_B))))
% 0.44/0.63          | (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.44/0.63      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.44/0.63  thf('14', plain,
% 0.44/0.63      (((r2_hidden @ 
% 0.44/0.63         (k1_funct_1 @ sk_B @ 
% 0.44/0.63          (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))) @ 
% 0.44/0.63         k1_xboole_0)
% 0.44/0.63        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.44/0.63        | ~ (v1_relat_1 @ sk_A)
% 0.44/0.63        | ~ (v1_funct_1 @ sk_A)
% 0.44/0.63        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.44/0.63      inference('sup+', [status(thm)], ['3', '13'])).
% 0.44/0.63  thf('15', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i]:
% 0.44/0.63         (((k1_funct_1 @ X0 @ (sk_C @ (k1_relat_1 @ X0) @ X1)) = (k1_xboole_0))
% 0.44/0.63          | ~ (v1_funct_1 @ X0)
% 0.44/0.63          | ~ (v1_relat_1 @ X0)
% 0.44/0.63          | (r1_tarski @ X1 @ (k1_relat_1 @ X0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.63  thf('16', plain, ((v5_funct_1 @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('17', plain,
% 0.44/0.63      (![X11 : $i, X12 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X12)
% 0.44/0.63          | ~ (v1_funct_1 @ X12)
% 0.44/0.63          | ((k1_funct_1 @ X12 @ X11) = (k1_xboole_0))
% 0.44/0.63          | (r2_hidden @ X11 @ (k1_relat_1 @ X12)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['0'])).
% 0.44/0.63  thf('18', plain,
% 0.44/0.63      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X8)
% 0.44/0.63          | ~ (v1_funct_1 @ X8)
% 0.44/0.63          | ~ (v5_funct_1 @ X8 @ X9)
% 0.44/0.63          | (r2_hidden @ (k1_funct_1 @ X8 @ X10) @ (k1_funct_1 @ X9 @ X10))
% 0.44/0.63          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X8))
% 0.44/0.63          | ~ (v1_funct_1 @ X9)
% 0.44/0.63          | ~ (v1_relat_1 @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.44/0.63  thf('19', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.44/0.63          | ~ (v1_funct_1 @ X0)
% 0.44/0.63          | ~ (v1_relat_1 @ X0)
% 0.44/0.63          | ~ (v1_relat_1 @ X2)
% 0.44/0.63          | ~ (v1_funct_1 @ X2)
% 0.44/0.63          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k1_funct_1 @ X2 @ X1))
% 0.44/0.63          | ~ (v5_funct_1 @ X0 @ X2)
% 0.44/0.63          | ~ (v1_funct_1 @ X0)
% 0.44/0.63          | ~ (v1_relat_1 @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.63  thf('20', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (~ (v5_funct_1 @ X0 @ X2)
% 0.44/0.63          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k1_funct_1 @ X2 @ X1))
% 0.44/0.63          | ~ (v1_funct_1 @ X2)
% 0.44/0.63          | ~ (v1_relat_1 @ X2)
% 0.44/0.63          | ~ (v1_relat_1 @ X0)
% 0.44/0.63          | ~ (v1_funct_1 @ X0)
% 0.44/0.63          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.44/0.63      inference('simplify', [status(thm)], ['19'])).
% 0.44/0.63  thf('21', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.44/0.63          | ~ (v1_funct_1 @ sk_B)
% 0.44/0.63          | ~ (v1_relat_1 @ sk_B)
% 0.44/0.63          | ~ (v1_relat_1 @ sk_A)
% 0.44/0.63          | ~ (v1_funct_1 @ sk_A)
% 0.44/0.63          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k1_funct_1 @ sk_A @ X0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['16', '20'])).
% 0.44/0.64  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('25', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('26', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (((k1_funct_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.44/0.64          | (r2_hidden @ (k1_funct_1 @ sk_B @ X0) @ (k1_funct_1 @ sk_A @ X0)))),
% 0.44/0.64      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.44/0.64  thf('27', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((r2_hidden @ 
% 0.44/0.64           (k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0)) @ 
% 0.44/0.64           k1_xboole_0)
% 0.44/0.64          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 0.44/0.64          | ~ (v1_relat_1 @ sk_A)
% 0.44/0.64          | ~ (v1_funct_1 @ sk_A)
% 0.44/0.64          | ((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.44/0.64              = (k1_xboole_0)))),
% 0.44/0.64      inference('sup+', [status(thm)], ['15', '26'])).
% 0.44/0.64  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('29', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('30', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((r2_hidden @ 
% 0.44/0.64           (k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0)) @ 
% 0.44/0.64           k1_xboole_0)
% 0.44/0.64          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 0.44/0.64          | ((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.44/0.64              = (k1_xboole_0)))),
% 0.44/0.64      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.44/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.64  thf('31', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.44/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.64  thf('32', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.44/0.64          | (r2_hidden @ X0 @ X2)
% 0.44/0.64          | ~ (r1_tarski @ X1 @ X2))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.64  thf('33', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.64  thf('34', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.44/0.64            = (k1_xboole_0))
% 0.44/0.64          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 0.44/0.64          | (r2_hidden @ 
% 0.44/0.64             (k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0)) @ X1))),
% 0.44/0.64      inference('sup-', [status(thm)], ['30', '33'])).
% 0.44/0.64  thf(t7_tarski, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ~( ( r2_hidden @ A @ B ) & 
% 0.44/0.64          ( ![C:$i]:
% 0.44/0.64            ( ~( ( r2_hidden @ C @ B ) & 
% 0.44/0.64                 ( ![D:$i]:
% 0.44/0.64                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.44/0.64  thf('35', plain,
% 0.44/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X5 @ X6)
% 0.44/0.64          | ~ (r2_hidden @ X7 @ X6)
% 0.44/0.64          | ~ (r2_hidden @ X7 @ (sk_C_1 @ X6)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t7_tarski])).
% 0.44/0.64  thf('36', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.44/0.64      inference('condensation', [status(thm)], ['35'])).
% 0.44/0.64  thf('37', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         ((r1_tarski @ X1 @ (k1_relat_1 @ sk_A))
% 0.44/0.64          | ((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X1))
% 0.44/0.64              = (k1_xboole_0))
% 0.44/0.64          | ~ (r2_hidden @ 
% 0.44/0.64               (k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X1)) @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['34', '36'])).
% 0.44/0.64  thf('38', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0))
% 0.44/0.64            = (k1_xboole_0))
% 0.44/0.64          | (r1_tarski @ X0 @ (k1_relat_1 @ sk_A))
% 0.44/0.64          | (r2_hidden @ 
% 0.44/0.64             (k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X0)) @ X1))),
% 0.44/0.64      inference('sup-', [status(thm)], ['30', '33'])).
% 0.44/0.64  thf('39', plain,
% 0.44/0.64      (![X1 : $i]:
% 0.44/0.64         (((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ X1))
% 0.44/0.64            = (k1_xboole_0))
% 0.44/0.64          | (r1_tarski @ X1 @ (k1_relat_1 @ sk_A)))),
% 0.44/0.64      inference('clc', [status(thm)], ['37', '38'])).
% 0.44/0.64  thf('40', plain,
% 0.44/0.64      (![X1 : $i, X3 : $i]:
% 0.44/0.64         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.64      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.64  thf('41', plain,
% 0.44/0.64      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.44/0.64          | (r2_hidden @ (k4_tarski @ X11 @ X14) @ X12)
% 0.44/0.64          | ((X14) != (k1_funct_1 @ X12 @ X11))
% 0.44/0.64          | ~ (v1_funct_1 @ X12)
% 0.44/0.64          | ~ (v1_relat_1 @ X12))),
% 0.44/0.64      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.44/0.64  thf('42', plain,
% 0.44/0.64      (![X11 : $i, X12 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X12)
% 0.44/0.64          | ~ (v1_funct_1 @ X12)
% 0.44/0.64          | (r2_hidden @ (k4_tarski @ X11 @ (k1_funct_1 @ X12 @ X11)) @ X12)
% 0.44/0.64          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X12)))),
% 0.44/0.64      inference('simplify', [status(thm)], ['41'])).
% 0.44/0.64  thf('43', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.44/0.64          | (r2_hidden @ 
% 0.44/0.64             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.44/0.64              (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0)))) @ 
% 0.44/0.64             X0)
% 0.44/0.64          | ~ (v1_funct_1 @ X0)
% 0.44/0.64          | ~ (v1_relat_1 @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['40', '42'])).
% 0.44/0.64  thf('44', plain,
% 0.44/0.64      (((r2_hidden @ 
% 0.44/0.64         (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.44/0.64          k1_xboole_0) @ 
% 0.44/0.64         sk_B)
% 0.44/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.44/0.64        | ~ (v1_relat_1 @ sk_B)
% 0.44/0.64        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.44/0.64      inference('sup+', [status(thm)], ['39', '43'])).
% 0.44/0.64  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('47', plain,
% 0.44/0.64      (((r2_hidden @ 
% 0.44/0.64         (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.44/0.64          k1_xboole_0) @ 
% 0.44/0.64         sk_B)
% 0.44/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.44/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.44/0.64  thf('48', plain,
% 0.44/0.64      (((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.44/0.64        | (r2_hidden @ 
% 0.44/0.64           (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.44/0.64            k1_xboole_0) @ 
% 0.44/0.64           sk_B))),
% 0.44/0.64      inference('simplify', [status(thm)], ['47'])).
% 0.44/0.64  thf('49', plain, (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('50', plain,
% 0.44/0.64      ((r2_hidden @ 
% 0.44/0.64        (k4_tarski @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ 
% 0.44/0.64         k1_xboole_0) @ 
% 0.44/0.64        sk_B)),
% 0.44/0.64      inference('clc', [status(thm)], ['48', '49'])).
% 0.44/0.64  thf('51', plain,
% 0.44/0.64      (![X11 : $i, X12 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X12)
% 0.44/0.64          | ~ (v1_funct_1 @ X12)
% 0.44/0.64          | ((k1_funct_1 @ X12 @ X11) = (k1_xboole_0))
% 0.44/0.64          | (r2_hidden @ X11 @ (k1_relat_1 @ X12)))),
% 0.44/0.64      inference('simplify', [status(thm)], ['0'])).
% 0.44/0.64  thf('52', plain,
% 0.44/0.64      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.44/0.64          | ((X14) = (k1_funct_1 @ X12 @ X11))
% 0.44/0.64          | ~ (r2_hidden @ (k4_tarski @ X11 @ X14) @ X12)
% 0.44/0.64          | ~ (v1_funct_1 @ X12)
% 0.44/0.64          | ~ (v1_relat_1 @ X12))),
% 0.44/0.64      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.44/0.64  thf('53', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.44/0.64          | ~ (v1_funct_1 @ X0)
% 0.44/0.64          | ~ (v1_relat_1 @ X0)
% 0.44/0.64          | ~ (v1_relat_1 @ X0)
% 0.44/0.64          | ~ (v1_funct_1 @ X0)
% 0.44/0.64          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.44/0.64          | ((X2) = (k1_funct_1 @ X0 @ X1)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['51', '52'])).
% 0.44/0.64  thf('54', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (((X2) = (k1_funct_1 @ X0 @ X1))
% 0.44/0.64          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.44/0.64          | ~ (v1_relat_1 @ X0)
% 0.44/0.64          | ~ (v1_funct_1 @ X0)
% 0.44/0.64          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.44/0.64      inference('simplify', [status(thm)], ['53'])).
% 0.44/0.64  thf('55', plain,
% 0.44/0.64      ((((k1_funct_1 @ sk_B @ 
% 0.44/0.64          (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))) = (k1_xboole_0))
% 0.44/0.64        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.64        | ~ (v1_relat_1 @ sk_B)
% 0.44/0.64        | ((k1_xboole_0)
% 0.44/0.64            = (k1_funct_1 @ sk_B @ 
% 0.44/0.64               (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['50', '54'])).
% 0.44/0.64  thf('56', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('58', plain,
% 0.44/0.64      ((((k1_funct_1 @ sk_B @ 
% 0.44/0.64          (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))) = (k1_xboole_0))
% 0.44/0.64        | ((k1_xboole_0)
% 0.44/0.64            = (k1_funct_1 @ sk_B @ 
% 0.44/0.64               (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))))),
% 0.44/0.64      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.44/0.64  thf('59', plain,
% 0.44/0.64      (((k1_funct_1 @ sk_B @ (sk_C @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.44/0.64         = (k1_xboole_0))),
% 0.44/0.64      inference('simplify', [status(thm)], ['58'])).
% 0.44/0.64  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('61', plain, ((v1_funct_1 @ sk_A)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('62', plain,
% 0.44/0.64      (((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.44/0.64        | (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['14', '59', '60', '61'])).
% 0.44/0.64  thf('63', plain,
% 0.44/0.64      (((r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))
% 0.44/0.64        | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.44/0.64      inference('simplify', [status(thm)], ['62'])).
% 0.44/0.64  thf('64', plain, (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('65', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.44/0.64      inference('clc', [status(thm)], ['63', '64'])).
% 0.44/0.64  thf('66', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.64  thf('67', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ X0)),
% 0.44/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.44/0.64  thf('68', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.44/0.64      inference('condensation', [status(thm)], ['35'])).
% 0.44/0.64  thf('69', plain, (![X0 : $i]: ~ (r2_hidden @ k1_xboole_0 @ X0)),
% 0.44/0.64      inference('sup-', [status(thm)], ['67', '68'])).
% 0.44/0.64  thf('70', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ X0)),
% 0.44/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.44/0.64  thf('71', plain, ($false), inference('demod', [status(thm)], ['69', '70'])).
% 0.44/0.64  
% 0.44/0.64  % SZS output end Refutation
% 0.44/0.64  
% 0.44/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
