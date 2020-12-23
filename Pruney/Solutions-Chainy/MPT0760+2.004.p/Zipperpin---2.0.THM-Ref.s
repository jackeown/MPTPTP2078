%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iTWBk4lwbw

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 116 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   24
%              Number of atoms          :  620 ( 823 expanded)
%              Number of equality atoms :   52 (  70 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t2_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
        | ( ( k1_wellord1 @ B @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
          | ( ( k1_wellord1 @ B @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_wellord1])).

thf('0',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ ( sk_D @ X23 @ X24 @ X25 ) @ X23 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X23 @ X24 @ X25 ) @ X24 ) @ X25 )
      | ( X23
        = ( k1_wellord1 @ X25 @ X24 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X10 @ ( k3_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t18_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_relat_1 @ C ) )
           => ~ ( ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
                & ( B
                  = ( k1_relat_1 @ C ) ) ) )
        & ~ ( ( B != k1_xboole_0 )
            & ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ C )
       => ~ ( zip_tseitin_1 @ C @ B @ A ) )
     => ( zip_tseitin_2 @ C @ B @ A ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X16 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X16 @ X17 @ X18 )
      | ( zip_tseitin_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
     => ( ( A = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B
          = ( k1_relat_1 @ C ) )
        & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i] :
      ( ( zip_tseitin_0 @ C )
     => ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) ) ) )).

thf(zf_stmt_9,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( zip_tseitin_3 @ B @ A )
        & ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_3 @ X21 @ X22 )
      | ~ ( zip_tseitin_2 @ ( sk_C_1 @ X21 @ X22 ) @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( zip_tseitin_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X16 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_3 @ X21 @ X22 )
      | ~ ( zip_tseitin_2 @ ( sk_C_1 @ X21 @ X22 ) @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_C_1 @ X1 @ X0 ) @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k1_relat_1 @ X13 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t196_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( ( k1_relat_1 @ A )
                = k1_xboole_0 )
              & ( ( k1_relat_1 @ B )
                = k1_xboole_0 ) )
           => ( A = B ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( X8 = X7 )
      | ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X8 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t196_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( zip_tseitin_3 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
       != k1_xboole_0 )
      | ( X2
        = ( sk_C_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C_1 @ k1_xboole_0 @ X1 ) )
      | ( X2
        = ( sk_C_1 @ k1_xboole_0 @ X1 ) )
      | ( ( k1_relat_1 @ X2 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != k1_xboole_0 )
      | ( X1
        = ( sk_C_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ k1_xboole_0 @ X0 )
      | ( X1
        = ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k1_relat_1 @ X1 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != k1_xboole_0 )
      | ( X1
        = ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','25'])).

thf('27',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( sk_C_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 != k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X19: $i] :
      ~ ( zip_tseitin_3 @ k1_xboole_0 @ X19 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( sk_C_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_3 @ X21 @ X22 )
      | ~ ( zip_tseitin_2 @ ( sk_C_1 @ X21 @ X22 ) @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X19: $i] :
      ~ ( zip_tseitin_3 @ k1_xboole_0 @ X19 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','36'])).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X15 )
      | ~ ( zip_tseitin_1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','43'])).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X26
       != ( k1_wellord1 @ X25 @ X24 ) )
      | ( X27 != X24 )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k1_wellord1 @ X25 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( k1_xboole_0
        = ( k1_wellord1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_wellord1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ( k1_wellord1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iTWBk4lwbw
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:45:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 80 iterations in 0.044s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.50  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.21/0.50  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.21/0.50  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $o).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(t2_wellord1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.21/0.50         ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( v1_relat_1 @ B ) =>
% 0.21/0.50          ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.21/0.50            ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t2_wellord1])).
% 0.21/0.50  thf('0', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t2_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.50  thf(fc1_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.50  thf(d1_wellord1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i,C:$i]:
% 0.21/0.50         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.21/0.50           ( ![D:$i]:
% 0.21/0.50             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.50               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ X23 @ X24 @ X25) @ X23)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ (sk_D @ X23 @ X24 @ X25) @ X24) @ X25)
% 0.21/0.50          | ((X23) = (k1_wellord1 @ X25 @ X24))
% 0.21/0.50          | ~ (v1_relat_1 @ X25))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.21/0.50  thf(t30_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ C ) =>
% 0.21/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.50         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.50           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.21/0.50          | (r2_hidden @ X10 @ (k3_relat_1 @ X11))
% 0.21/0.50          | ~ (v1_relat_1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((X2) = (k1_wellord1 @ X0 @ X1))
% 0.21/0.50          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.21/0.50          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.21/0.50          | ((X2) = (k1_wellord1 @ X0 @ X1))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.50  thf(t18_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ~( ( ![C:$i]:
% 0.21/0.50            ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.21/0.50              ( ~( ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.21/0.50                   ( ( B ) = ( k1_relat_1 @ C ) ) ) ) ) ) & 
% 0.21/0.50          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_1, axiom,
% 0.21/0.50    (![C:$i,B:$i,A:$i]:
% 0.21/0.50     ( ( ( zip_tseitin_0 @ C ) => ( ~( zip_tseitin_1 @ C @ B @ A ) ) ) =>
% 0.21/0.50       ( zip_tseitin_2 @ C @ B @ A ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.50         ((zip_tseitin_2 @ X16 @ X17 @ X18) | (zip_tseitin_1 @ X16 @ X17 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf(t60_relat_1, axiom,
% 0.21/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('10', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.50         ((zip_tseitin_2 @ X16 @ X17 @ X18) | (zip_tseitin_0 @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf(zf_stmt_2, type, zip_tseitin_3 : $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_3, axiom,
% 0.21/0.50    (![B:$i,A:$i]:
% 0.21/0.50     ( ( zip_tseitin_3 @ B @ A ) =>
% 0.21/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_6, axiom,
% 0.21/0.50    (![C:$i,B:$i,A:$i]:
% 0.21/0.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.50       ( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.50         ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ))).
% 0.21/0.50  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $o).
% 0.21/0.50  thf(zf_stmt_8, axiom,
% 0.21/0.50    (![C:$i]:
% 0.21/0.50     ( ( zip_tseitin_0 @ C ) => ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) ))).
% 0.21/0.50  thf(zf_stmt_9, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ~( ( ~( zip_tseitin_3 @ B @ A ) ) & 
% 0.21/0.50          ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         ((zip_tseitin_3 @ X21 @ X22)
% 0.21/0.50          | ~ (zip_tseitin_2 @ (sk_C_1 @ X21 @ X22) @ X21 @ X22))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((zip_tseitin_0 @ (sk_C_1 @ X1 @ X0)) | (zip_tseitin_3 @ X1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X12 : $i]: ((v1_relat_1 @ X12) | ~ (zip_tseitin_0 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.50         ((zip_tseitin_2 @ X16 @ X17 @ X18) | (zip_tseitin_1 @ X16 @ X17 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         ((zip_tseitin_3 @ X21 @ X22)
% 0.21/0.50          | ~ (zip_tseitin_2 @ (sk_C_1 @ X21 @ X22) @ X21 @ X22))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((zip_tseitin_1 @ (sk_C_1 @ X1 @ X0) @ X1 @ X0)
% 0.21/0.50          | (zip_tseitin_3 @ X1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         (((X14) = (k1_relat_1 @ X13)) | ~ (zip_tseitin_1 @ X13 @ X14 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((zip_tseitin_3 @ X1 @ X0)
% 0.21/0.50          | ((X1) = (k1_relat_1 @ (sk_C_1 @ X1 @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf(t196_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v1_relat_1 @ B ) =>
% 0.21/0.50           ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.50               ( ( k1_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.50             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X7)
% 0.21/0.50          | ((X8) = (X7))
% 0.21/0.50          | ((k1_relat_1 @ X7) != (k1_xboole_0))
% 0.21/0.50          | ((k1_relat_1 @ X8) != (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t196_relat_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((X0) != (k1_xboole_0))
% 0.21/0.50          | (zip_tseitin_3 @ X0 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X2)
% 0.21/0.50          | ((k1_relat_1 @ X2) != (k1_xboole_0))
% 0.21/0.50          | ((X2) = (sk_C_1 @ X0 @ X1))
% 0.21/0.50          | ~ (v1_relat_1 @ (sk_C_1 @ X0 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (sk_C_1 @ k1_xboole_0 @ X1))
% 0.21/0.50          | ((X2) = (sk_C_1 @ k1_xboole_0 @ X1))
% 0.21/0.50          | ((k1_relat_1 @ X2) != (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X2)
% 0.21/0.50          | (zip_tseitin_3 @ k1_xboole_0 @ X1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (zip_tseitin_0 @ (sk_C_1 @ k1_xboole_0 @ X0))
% 0.21/0.50          | (zip_tseitin_3 @ k1_xboole_0 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X1)
% 0.21/0.50          | ((k1_relat_1 @ X1) != (k1_xboole_0))
% 0.21/0.50          | ((X1) = (sk_C_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((zip_tseitin_3 @ k1_xboole_0 @ X0)
% 0.21/0.50          | ((X1) = (sk_C_1 @ k1_xboole_0 @ X0))
% 0.21/0.50          | ((k1_relat_1 @ X1) != (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X1)
% 0.21/0.50          | (zip_tseitin_3 @ k1_xboole_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X1)
% 0.21/0.50          | ((k1_relat_1 @ X1) != (k1_xboole_0))
% 0.21/0.50          | ((X1) = (sk_C_1 @ k1_xboole_0 @ X0))
% 0.21/0.50          | (zip_tseitin_3 @ k1_xboole_0 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50          | (zip_tseitin_3 @ k1_xboole_0 @ X0)
% 0.21/0.50          | ((k1_xboole_0) = (sk_C_1 @ k1_xboole_0 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '25'])).
% 0.21/0.50  thf('27', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50          | (zip_tseitin_3 @ k1_xboole_0 @ X0)
% 0.21/0.50          | ((k1_xboole_0) = (sk_C_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_xboole_0) = (sk_C_1 @ k1_xboole_0 @ X0))
% 0.21/0.50          | (zip_tseitin_3 @ k1_xboole_0 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i]:
% 0.21/0.50         (((X20) != (k1_xboole_0)) | ~ (zip_tseitin_3 @ X20 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('31', plain, (![X19 : $i]: ~ (zip_tseitin_3 @ k1_xboole_0 @ X19)),
% 0.21/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.50  thf('32', plain, (![X0 : $i]: ((k1_xboole_0) = (sk_C_1 @ k1_xboole_0 @ X0))),
% 0.21/0.50      inference('clc', [status(thm)], ['29', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         ((zip_tseitin_3 @ X21 @ X22)
% 0.21/0.50          | ~ (zip_tseitin_2 @ (sk_C_1 @ X21 @ X22) @ X21 @ X22))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.50          | (zip_tseitin_3 @ k1_xboole_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain, (![X19 : $i]: ~ (zip_tseitin_3 @ k1_xboole_0 @ X19)),
% 0.21/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i]: ~ (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.50      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((r1_tarski @ (k2_relat_1 @ X13) @ X15)
% 0.21/0.50          | ~ (zip_tseitin_1 @ X13 @ X14 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.50  thf('39', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('41', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((k1_xboole_0) = (k1_wellord1 @ X0 @ X1))
% 0.21/0.50          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.21/0.50          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '43'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.50         (((X26) != (k1_wellord1 @ X25 @ X24))
% 0.21/0.50          | ((X27) != (X24))
% 0.21/0.50          | ~ (r2_hidden @ X27 @ X26)
% 0.21/0.50          | ~ (v1_relat_1 @ X25))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X25)
% 0.21/0.50          | ~ (r2_hidden @ X24 @ (k1_wellord1 @ X25 @ X24)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.21/0.50          | ((k1_xboole_0) = (k1_wellord1 @ X0 @ X1))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.50  thf('48', plain, (~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.50          | ((k1_xboole_0) = (k1_wellord1 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0) | ((k1_xboole_0) = (k1_wellord1 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.50  thf('52', plain, (((k1_wellord1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('53', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.21/0.50  thf('54', plain, ($false), inference('sup-', [status(thm)], ['4', '53'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
